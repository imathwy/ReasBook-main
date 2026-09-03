from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from reasbook_build_sdk import BuildOptions, discover_project, plan_build, shell_preview


class LakePlanTests(unittest.TestCase):
    def test_cache_precedes_build_and_targets_are_deduplicated(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "demo"
            root.mkdir()
            (root / "lakefile.toml").write_text("name = 'Demo'\n", encoding="utf-8")
            (root / "lean-toolchain").write_text(
                "leanprover/lean4:v4.30.0\n", encoding="utf-8"
            )
            options = BuildOptions.from_values(targets=("Demo:docs", "Demo:docs"))
            plan = plan_build(root, options)
        self.assertEqual(len(plan.commands), 2)
        self.assertEqual(plan.commands[0].argv[1:], ("exe", "cache", "get"))
        self.assertEqual(plan.commands[1].argv[1:], ("build", "Demo:docs"))
        self.assertLess(
            shell_preview(plan).index("cache get"), shell_preview(plan).index("build")
        )

    def test_skip_cache_produces_only_build_command(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "demo"
            root.mkdir()
            (root / "lakefile.toml").write_text("name = 'Demo'\n", encoding="utf-8")
            (root / "lean-toolchain").write_text(
                "leanprover/lean4:v4.30.0\n", encoding="utf-8"
            )
            plan = plan_build(
                discover_project(root), BuildOptions.from_values(run_cache_get=False)
            )
        self.assertEqual(len(plan.commands), 1)
        self.assertEqual(plan.commands[0].argv[:2], ("lake", "build"))

    def test_lake_args_are_inserted_before_subcommand(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "demo"
            root.mkdir()
            (root / "lakefile.toml").write_text("name = 'Demo'\n", encoding="utf-8")
            (root / "lean-toolchain").write_text(
                "leanprover/lean4:v4.30.0\n", encoding="utf-8"
            )
            plan = plan_build(
                root,
                BuildOptions.from_values(
                    targets=("Demo:docs",),
                    lake_args=("-R", "-Kenv=dev"),
                    run_cache_get=False,
                ),
            )
        self.assertEqual(
            plan.commands[0].argv,
            ("lake", "-R", "-Kenv=dev", "build", "Demo:docs"),
        )


if __name__ == "__main__":
    unittest.main()
