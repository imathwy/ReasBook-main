from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from reasbook_build_sdk import (
    BuildOptions,
    BuildService,
    CallableRunner,
    CommandResult,
    LocalBuildExecutor,
)


def project(root: Path) -> Path:
    root.mkdir(parents=True)
    (root / "lakefile.toml").write_text("name = 'Demo'\n", encoding="utf-8")
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.30.0\n", encoding="utf-8")
    return root


class ServiceTests(unittest.TestCase):
    def test_local_executor_runs_commands_in_order_and_verifies_output(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = project(Path(tmp) / "demo")
            calls: list[str] = []

            def run(command):
                calls.append(command.display)
                if command.argv[1:] == ("build",):
                    output = root / ".lake" / "build" / "lib" / "lean" / "Demo.olean"
                    output.parent.mkdir(parents=True)
                    output.write_bytes(b"olean")
                return CommandResult(command=command, returncode=0)

            service = BuildService(LocalBuildExecutor(CallableRunner(run)))
            result = service.run(root, BuildOptions.from_values())
        self.assertTrue(result.succeeded)
        self.assertEqual(len(calls), 2)
        self.assertEqual(result.artifacts[0].name, "Demo.olean")

    def test_failed_command_stops_the_plan(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = project(Path(tmp) / "demo")

            def run(command):
                return CommandResult(command=command, returncode=7)

            result = BuildService(LocalBuildExecutor(CallableRunner(run))).run(
                root, BuildOptions.from_values()
            )
        self.assertEqual(result.status, "failed")
        self.assertEqual(len(result.command_results), 1)

    def test_injected_plan_executor_is_supported(self) -> None:
        class FakeExecutor:
            def execute(self, plan):
                from reasbook_build_sdk import BuildResult

                return BuildResult(
                    plan=plan, status="success", message="handled externally"
                )

        with tempfile.TemporaryDirectory() as tmp:
            root = project(Path(tmp) / "demo")
            result = BuildService(FakeExecutor()).run(root, BuildOptions.from_values())
        self.assertTrue(result.succeeded)
        self.assertEqual(result.message, "handled externally")


if __name__ == "__main__":
    unittest.main()
