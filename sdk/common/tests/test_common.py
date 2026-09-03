from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest

from reasbook_sdk_common import (
    Command,
    CommandResult,
    CommandRunner,
    CommandTimeoutError,
    atomic_write_json,
    ensure_within,
    safe_relative,
)


class CommonSdkTests(unittest.TestCase):
    def test_command_normalizes_environment_and_result(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            command = Command(
                ("printf", "ok"),
                cwd=Path(temp),
                env={"EMPTY": ""},
                timeout=2,
            )
            result = CommandResult(command=command, returncode=0)
        self.assertEqual(command.env_dict, {"EMPTY": ""})
        self.assertEqual(result.argv, ("printf", "ok"))
        self.assertTrue(result.succeeded)

    def test_unsafe_paths_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve()
            self.assertEqual(ensure_within(root / "child", root), root / "child")
            with self.assertRaises(ValueError):
                ensure_within(root.parent, root)
        with self.assertRaises(ValueError):
            safe_relative("../outside")

    def test_atomic_json_write_is_readable(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            destination = Path(temp) / "nested" / "result.json"
            atomic_write_json(destination, {"b": 2, "a": 1})
            self.assertEqual(
                json.loads(destination.read_text(encoding="utf-8")), {"a": 1, "b": 2}
            )

    def test_timeout_terminates_the_process_group(self) -> None:
        command = Command(
            (sys.executable, "-c", "import time; time.sleep(30)"),
            timeout=0.05,
        )
        with self.assertRaises(CommandTimeoutError):
            CommandRunner().run(command)

    def test_output_file_keeps_large_runner_output_off_result_memory(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            log = Path(temp) / "run.log"
            result = CommandRunner(output_file=log).run(
                Command((sys.executable, "-c", "print('logged')"))
            )
            self.assertTrue(result.succeeded)
            self.assertEqual(result.stdout, "")
            self.assertIn("logged", log.read_text(encoding="utf-8"))

    def test_active_command_can_be_cancelled_from_supervisor_thread(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            ready = Path(temp) / "ready"
            runner = CommandRunner()
            results = []
            thread = threading.Thread(
                target=lambda: results.append(
                    runner.run(
                        Command(
                            (
                                sys.executable,
                                "-c",
                                (
                                    "from pathlib import Path; import time; "
                                    f"Path({str(ready)!r}).write_text('ready'); "
                                    "time.sleep(30)"
                                ),
                            )
                        )
                    )
                )
            )
            thread.start()
            deadline = time.monotonic() + 5
            while not ready.is_file() and time.monotonic() < deadline:
                time.sleep(0.01)
            self.assertTrue(ready.is_file())
            runner.terminate()
            thread.join(timeout=5)
            self.assertFalse(thread.is_alive())
            self.assertEqual(len(results), 1)
            self.assertNotEqual(results[0].returncode, 0)


if __name__ == "__main__":
    unittest.main()
