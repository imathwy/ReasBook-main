from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from reasbook_sdk_common import Command, CommandResult

from verso_build_sdk import (
    VersoBuildConfig,
    VersoBuilder,
    discover_project,
    lake_argv,
)
from verso_build_sdk.errors import CommandExecutionError


class RecordingRunner:
    def __init__(self) -> None:
        self.calls: list[tuple[tuple[str, ...], Path]] = []

    def run(self, command: Command):
        self.calls.append((tuple(command.argv), command.cwd))
        return CommandResult(argv=command.argv, command=command, returncode=0)


class FailingRunner(RecordingRunner):
    def run(self, command: Command):
        self.calls.append((tuple(command.argv), command.cwd))
        return CommandResult(
            argv=command.argv,
            command=command,
            returncode=7,
            stderr="failed",
        )


class VersoSdkTests(unittest.TestCase):
    def project(self, root: Path) -> None:
        (root / "lakefile.lean").write_text(
            'import Lake\npackage "demo-site" where\n', encoding="utf-8"
        )
        (root / "lean-toolchain").write_text(
            "leanprover/lean4:v4.26.0\n", encoding="utf-8"
        )

    def test_discovery_reads_package_and_toolchain(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            self.project(root)
            project = discover_project(root, require_toolchain=True)
            self.assertEqual(project.package_name, "demo-site")
            self.assertEqual(project.toolchain, "leanprover/lean4:v4.26.0")

    def test_lake_argv_is_not_a_shell_string(self) -> None:
        config = VersoBuildConfig(
            web_root=Path("/tmp/site").resolve(),
            toolchain="leanprover/lean4:v4.26.0",
            targets=("exe", "site"),
        )
        self.assertEqual(
            lake_argv(config),
            (
                "elan",
                "run",
                "--install",
                "leanprover/lean4:v4.26.0",
                "lake",
                "exe",
                "site",
            ),
        )

    def test_builder_runs_generator_then_build(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            self.project(root)
            runner = RecordingRunner()
            config = VersoBuildConfig(
                web_root=root,
                toolchain=None,
                generator=("python3", "generate.py"),
                targets=("exe", "site"),
            )
            result = VersoBuilder(
                config, runner=runner, environ={"LAKE": "bad", "KEEP": "yes"}
            ).run()
            self.assertFalse(result.dry_run)
            self.assertEqual(
                [call[0] for call in runner.calls],
                [
                    ("python3", "generate.py"),
                    (
                        "elan",
                        "run",
                        "--install",
                        "leanprover/lean4:v4.26.0",
                        "lake",
                        "exe",
                        "site",
                    ),
                ],
            )

    def test_dry_run_does_not_execute(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            self.project(root)
            runner = RecordingRunner()
            result = VersoBuilder(VersoBuildConfig(web_root=root), runner=runner).run(
                dry_run=True
            )
            self.assertTrue(result.dry_run)
            self.assertEqual(runner.calls, [])

    def test_runner_failure_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            self.project(root)
            with self.assertRaises(CommandExecutionError):
                VersoBuilder(
                    VersoBuildConfig(web_root=root),
                    runner=FailingRunner(),
                ).run()


if __name__ == "__main__":
    unittest.main()
