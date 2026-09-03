"""Build-plan executors built on the shared command runner."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Mapping

from reasbook_sdk_common import (
    Command,
    CommandExecutionError,
    CommandResult,
    CommandRunner as SharedCommandRunner,
    CommandTimeoutError,
)

from .command import command_error


@dataclass
class SubprocessRunner:
    """Execute one command using the shared subprocess implementation."""

    stream: bool = False
    base_environment: Mapping[str, str] | None = None

    def run(self, command: Command) -> CommandResult:
        effective_command = command
        if self.base_environment is not None:
            effective_command = Command(
                argv=command.argv,
                cwd=command.cwd,
                env={**dict(self.base_environment), **command.env_dict},
                timeout=command.timeout,
                input_text=command.input_text,
            )
        try:
            return SharedCommandRunner(
                stream=self.stream,
                inherit_environment=self.base_environment is None,
            ).run(effective_command)
        except CommandTimeoutError:
            raise
        except CommandExecutionError as exc:
            raise command_error(command, str(exc), cause=exc) from exc


@dataclass
class CallableRunner:
    """Adapt a callable to the shared command-runner contract."""

    callback: Callable[[Command], CommandResult]

    def run(self, command: Command) -> CommandResult:
        result = self.callback(command)
        if not isinstance(result, CommandResult):
            raise TypeError("command runner callback must return CommandResult")
        if result.command is None:
            result = CommandResult(
                argv=result.argv,
                returncode=result.returncode,
                stdout=result.stdout,
                stderr=result.stderr,
                duration_seconds=result.duration_seconds,
                timed_out=result.timed_out,
                command=command,
            )
        return result


__all__ = ["CallableRunner", "SubprocessRunner"]
