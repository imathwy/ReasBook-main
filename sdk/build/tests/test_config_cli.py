from __future__ import annotations

import io
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

from reasbook_build_sdk.cli import main
from reasbook_build_sdk.config import load_build_options


class ConfigCliTests(unittest.TestCase):
    def test_environment_configuration_is_generic_and_explicit_wins(self) -> None:
        options = load_build_options(
            environ={
                "REASBOOK_BUILD_CACHE_GET": "false",
                "REASBOOK_BUILD_TARGETS": "Demo:docs, Demo:extra",
                "REASBOOK_BUILD_LAKE_ARGS": "-R,-Kenv=dev",
            },
            targets=("Demo:explicit",),
        )
        self.assertFalse(options.run_cache_get)
        self.assertEqual(options.targets, ("Demo:explicit",))
        self.assertEqual(options.lake_args, ("-R", "-Kenv=dev"))

    def test_plan_json_does_not_include_environment_values(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "demo"
            root.mkdir()
            (root / "lakefile.toml").write_text("name = 'Demo'\n", encoding="utf-8")
            (root / "lean-toolchain").write_text(
                "leanprover/lean4:v4.30.0\n", encoding="utf-8"
            )
            output = io.StringIO()
            with redirect_stdout(output):
                code = main(["plan", str(root), "--env", "TOKEN=secret", "--json"])
        self.assertEqual(code, 0)
        self.assertNotIn("secret", output.getvalue())
        self.assertIn('"commands"', output.getvalue())

    def test_cli_accepts_dash_prefixed_lake_arg(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "demo"
            root.mkdir()
            (root / "lakefile.toml").write_text("name = 'Demo'\n", encoding="utf-8")
            (root / "lean-toolchain").write_text("v4.30.0\n", encoding="utf-8")
            output = io.StringIO()
            with redirect_stdout(output):
                code = main(["plan", str(root), "--lake-arg", "-R", "--json"])
        self.assertEqual(code, 0)
        self.assertIn('"lake_args": [\n    "-R"', output.getvalue())

    def test_cache_command_honors_skip_flag(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "demo"
            root.mkdir()
            (root / "lakefile.toml").write_text("name = 'Demo'\n", encoding="utf-8")
            (root / "lean-toolchain").write_text("v4.30.0\n", encoding="utf-8")
            output = io.StringIO()
            with redirect_stdout(output):
                code = main(["cache", str(root), "--skip-cache-get"])
        self.assertEqual(code, 0)
        self.assertIn("skipped", output.getvalue())


if __name__ == "__main__":
    unittest.main()
