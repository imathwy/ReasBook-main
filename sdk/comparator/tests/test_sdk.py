from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from comparator_sdk import (
    ComparatorConfig,
    ComparatorRunner,
    discover_project,
    expected_olean,
    split_module_name,
    validate_comparator_json,
)
from comparator_sdk.errors import ComparatorConfigError
from reasbook_sdk_common import Command, CommandResult, CommandTimeoutError


class RecordingRunner:
    def __init__(self, *, compare_code: int = 0, fail_stage: str | None = None) -> None:
        self.calls: list[Command] = []
        self.compare_code = compare_code
        self.fail_stage = fail_stage

    def run(self, command: Command) -> CommandResult:
        self.calls.append(command)
        stage = (
            "compare"
            if "env" in command.argv
            else "build"
            if "build" in command.argv
            else "cache"
        )
        if stage == self.fail_stage:
            raise CommandTimeoutError(f"{stage} timed out")
        if stage == "build":
            binary = command.cwd / ".lake" / "build" / "bin" / "comparator"
            binary.parent.mkdir(parents=True, exist_ok=True)
            binary.write_text("fake", encoding="utf-8")
        code = self.compare_code if stage == "compare" else 0
        return CommandResult(
            tuple(command.argv),
            code,
            "accepted\n" if code == 0 else "rejected\n",
            "",
            0.01,
        )


def make_workspace() -> tuple[tempfile.TemporaryDirectory[str], Path, Path]:
    holder = tempfile.TemporaryDirectory()
    root = Path(holder.name)
    project = root / "project with spaces"
    comparator = root / "comparator"
    project.mkdir()
    comparator.mkdir()
    for directory, name in ((project, "Target"), (comparator, "Comparator")):
        (directory / "lakefile.toml").write_text(f'name = "{name}"\n', encoding="utf-8")
        (directory / "lean-toolchain").write_text(
            "leanprover/lean4:v4.30.0\n", encoding="utf-8"
        )
    (project / "configuration.json").write_text(
        json.dumps(
            {
                "challenge_module": "Challenge",
                "solution_module": "Solution",
                "theorem_names": ["comm"],
                "definition_names": [],
                "permitted_axioms": [],
            }
        ),
        encoding="utf-8",
    )
    return holder, project, comparator


class ComparatorSdkTests(unittest.TestCase):
    def test_discovery_and_quoted_module_names(self) -> None:
        holder, project, _ = make_workspace()
        self.addCleanup(holder.cleanup)
        discovered = discover_project(project)
        self.assertEqual(discovered.toolchain, "leanprover/lean4:v4.30.0")
        self.assertEqual(
            split_module_name("Challenge.«12.34».«5»"), ("Challenge", "12.34", "5")
        )

    def test_invalid_json_is_rejected(self) -> None:
        holder, project, _ = make_workspace()
        self.addCleanup(holder.cleanup)
        path = project / "bad.json"
        path.write_text('{"challenge_module": "Challenge"}', encoding="utf-8")
        with self.assertRaises(ComparatorConfigError):
            validate_comparator_json(path)

    def test_compare_uses_argv_and_accepts(self) -> None:
        holder, project, comparator = make_workspace()
        self.addCleanup(holder.cleanup)
        config = ComparatorConfig.from_paths(project, "configuration.json", comparator)
        runner = RecordingRunner()
        result = ComparatorRunner(config, runner=runner).compare()
        self.assertTrue(result.accepted)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(
            [command.argv[1] for command in runner.calls], ["build", "env"]
        )
        self.assertNotIsInstance(runner.calls[-1].argv, str)
        self.assertEqual(runner.calls[-1].cwd, project)

    def test_nonzero_comparator_is_a_rejection(self) -> None:
        holder, project, comparator = make_workspace()
        self.addCleanup(holder.cleanup)
        config = ComparatorConfig.from_paths(project, "configuration.json", comparator)
        result = ComparatorRunner(
            config, runner=RecordingRunner(compare_code=7)
        ).compare()
        self.assertTrue(result.rejected)
        self.assertEqual(result.returncode, 7)

    def test_preparation_timeout_is_not_a_rejection(self) -> None:
        holder, project, comparator = make_workspace()
        self.addCleanup(holder.cleanup)
        config = ComparatorConfig.from_paths(project, "configuration.json", comparator)
        runner = RecordingRunner(fail_stage="build")
        result = ComparatorRunner(config, runner=runner).compare()
        self.assertEqual(result.status, "timed_out")
        self.assertEqual(result.stage, "build")
        self.assertEqual(len(runner.calls), 1)

    def test_cache_and_result_file(self) -> None:
        holder, project, comparator = make_workspace()
        self.addCleanup(holder.cleanup)
        result_file = project / "results" / "comparison.json"
        config = ComparatorConfig.from_paths(
            project,
            "configuration.json",
            comparator,
            cache_before_compare=True,
            result_file=result_file,
        )
        runner = RecordingRunner()
        result = ComparatorRunner(config, runner=runner).compare()
        self.assertTrue(result.accepted)
        self.assertEqual(
            [command.argv[1] for command in runner.calls], ["exe", "build", "env"]
        )
        self.assertEqual(
            json.loads(result_file.read_text(encoding="utf-8"))["status"], "accepted"
        )

    def test_config_must_stay_inside_project(self) -> None:
        holder, project, comparator = make_workspace()
        self.addCleanup(holder.cleanup)
        outside = Path(holder.name) / "outside.json"
        outside.write_text("{}", encoding="utf-8")
        with self.assertRaises(ComparatorConfigError):
            ComparatorConfig.from_paths(project, outside, comparator)

    def test_from_env_uses_unambiguous_option_names(self) -> None:
        holder, project, comparator = make_workspace()
        self.addCleanup(holder.cleanup)
        config = ComparatorConfig.from_env(
            project,
            "configuration.json",
            comparator,
            environ={
                "COMPARATOR_BUILD": "false",
                "COMPARATOR_BIN": "bin/comparator",
                "COMPARATOR_TIMEOUT_SECONDS": "12",
                "COMPARATOR_ENV_FROM_ENV": "yes",
            },
            environment={"FROM_CLI": "yes"},
        )
        self.assertFalse(config.build_comparator)
        self.assertEqual(config.comparator_bin, comparator / "bin" / "comparator")
        self.assertEqual(config.timeout_seconds, 12.0)
        self.assertEqual(
            config.environment_dict,
            {"FROM_CLI": "yes", "FROM_ENV": "yes"},
        )

    def test_expected_olean_honors_custom_build_dir(self) -> None:
        holder, project, _ = make_workspace()
        self.addCleanup(holder.cleanup)
        (project / "lakefile.toml").write_text(
            '[package]\nname = "Target"\nbuildDir = "out"\n',
            encoding="utf-8",
        )
        output = project / "out" / "lib" / "lean" / "Challenge.olean"
        output.parent.mkdir(parents=True)
        output.write_bytes(b"olean")
        self.assertEqual(expected_olean(project, "Challenge"), output)


if __name__ == "__main__":
    unittest.main()
