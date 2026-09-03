from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from reasbook_build_sdk import Command, ConfigurationError


class CommandTests(unittest.TestCase):
    def test_commands_are_argument_vectors_and_preview_is_escaped(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            command = Command(
                argv=("lake", "build", "Target With Spaces"),
                cwd=Path(tmp) / "project with spaces",
                env=(("KEY", "value"),),
            )
        self.assertEqual(command.argv[1], "build")
        self.assertIn("'Target With Spaces'", command.display)
        self.assertEqual(command.env_dict, {"KEY": "value"})

    def test_empty_or_control_arguments_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(ConfigurationError):
                Command(argv=(), cwd=Path(tmp))
            with self.assertRaises(ConfigurationError):
                Command(argv=("lake\n",), cwd=Path(tmp))

    def test_empty_environment_values_are_valid(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            command = Command(argv=("lake",), cwd=Path(tmp), env=(("EMPTY", ""),))
        self.assertEqual(command.env_dict, {"EMPTY": ""})


if __name__ == "__main__":
    unittest.main()
