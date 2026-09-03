"""Build-specific command errors over shared process primitives."""

from __future__ import annotations

from reasbook_sdk_common import (
    Command as _CommonCommand,
    CommandExecutionError,
    CommandResult,
    CommandRunner,
    CommandTimeoutError,
    merged_environment,
    normalize_environment,
)

from .errors import CommandError, ConfigurationError


class Command(_CommonCommand):
    """Build SDK command with its historical configuration error type."""

    def __post_init__(self) -> None:
        try:
            super().__post_init__()
        except ValueError as exc:
            raise ConfigurationError(str(exc)) from exc


_normalize_env = normalize_environment


def command_error(
    command: Command,
    message: str,
    *,
    cause: BaseException | None = None,
) -> CommandError:
    """Create a consistently formatted build command error."""

    error = CommandError(
        f"could not execute {command.display} in {command.cwd}: {message}"
    )
    if cause is not None:
        error.__cause__ = cause
    return error


__all__ = [
    "Command",
    "CommandError",
    "CommandExecutionError",
    "CommandResult",
    "CommandRunner",
    "CommandTimeoutError",
    "_normalize_env",
    "command_error",
    "merged_environment",
]
