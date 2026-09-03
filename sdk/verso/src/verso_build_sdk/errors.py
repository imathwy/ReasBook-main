"""Errors raised by the transport-neutral Verso build SDK."""

from __future__ import annotations


class VersoBuildError(RuntimeError):
    """Base class for configuration, execution, and output errors."""


class ProjectValidationError(VersoBuildError):
    """The supplied directory is not a usable Lake/Verso project."""


class CommandExecutionError(VersoBuildError):
    """A generator or Lake command returned a non-zero exit status."""

    def __init__(
        self, command: tuple[str, ...], returncode: int, stderr: str = ""
    ) -> None:
        rendered = " ".join(command)
        suffix = f": {stderr.strip()}" if stderr.strip() else ""
        super().__init__(f"command exited with status {returncode}: {rendered}{suffix}")
        self.command = command
        self.returncode = returncode
        self.stderr = stderr
