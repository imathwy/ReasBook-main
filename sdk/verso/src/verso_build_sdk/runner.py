"""Injectable execution facade backed by the shared command runner."""

from __future__ import annotations

from typing import Protocol

from reasbook_sdk_common import (
    Command,
    CommandExecutionError as SharedCommandExecutionError,
    CommandResult,
    CommandRunner as SharedCommandRunner,
    CommandTimeoutError,
)

from .errors import CommandExecutionError


class CommandRunner(Protocol):
    def run(self, command: Command) -> CommandResult:
        """Execute one argv command and return its structured result."""


class SubprocessRunner:
    """Default runner; all process semantics come from the shared package."""

    def __init__(self, *, stream_output: bool = True) -> None:
        self._runner = SharedCommandRunner(stream=stream_output)

    def run(self, command: Command) -> CommandResult:
        try:
            return self._runner.run(command)
        except CommandTimeoutError as exc:
            raise CommandExecutionError(command.argv, 124, str(exc)) from exc
        except SharedCommandExecutionError as exc:
            raise CommandExecutionError(command.argv, 1, str(exc)) from exc


__all__ = ["CommandResult", "CommandRunner", "SubprocessRunner"]
