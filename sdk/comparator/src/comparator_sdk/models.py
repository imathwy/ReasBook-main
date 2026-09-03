"""Transport-neutral request and result models for Comparator."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Literal

from reasbook_sdk_common import Command, CommandResult

from .config import ComparatorConfig


ComparisonStatus = Literal["accepted", "rejected", "error", "timed_out", "planned"]


@dataclass(frozen=True)
class ComparatorRequest:
    """Commands planned for one comparison."""

    config: ComparatorConfig
    build_command: Command | None
    compare_command: Command
    cache_commands: tuple[Command, ...] = ()

    @property
    def commands(self) -> tuple[Command, ...]:
        commands = list(self.cache_commands)
        if self.build_command is not None:
            commands.append(self.build_command)
        commands.append(self.compare_command)
        return tuple(commands)

    def public_dict(self) -> dict[str, Any]:
        def describe(command: Command) -> dict[str, Any]:
            return {
                "argv": list(command.argv),
                "cwd": str(command.cwd) if command.cwd is not None else None,
                "timeout": command.timeout,
            }

        return {
            "config": self.config.public_dict(),
            "cache_commands": [describe(command) for command in self.cache_commands],
            "build_command": describe(self.build_command)
            if self.build_command
            else None,
            "compare_command": describe(self.compare_command),
        }


@dataclass(frozen=True)
class ComparisonResult:
    """Outcome of a local Comparator run."""

    status: ComparisonStatus
    returncode: int | None = None
    stdout: str = ""
    stderr: str = ""
    duration_seconds: float = 0.0
    stage: str = "compare"
    error: str | None = None
    command: tuple[str, ...] = field(default_factory=tuple)
    preparation: tuple[CommandResult, ...] = ()

    @property
    def accepted(self) -> bool:
        return self.status == "accepted"

    @property
    def rejected(self) -> bool:
        return self.status == "rejected"

    @property
    def succeeded(self) -> bool:
        """Whether Comparator accepted the candidate proof."""

        return self.accepted

    @property
    def exit_code(self) -> int | None:
        return self.returncode

    def public_dict(self) -> dict[str, Any]:
        return {
            "status": self.status,
            "accepted": self.accepted,
            "returncode": self.returncode,
            "stdout": self.stdout,
            "stderr": self.stderr,
            "duration_seconds": self.duration_seconds,
            "stage": self.stage,
            "error": self.error,
            "command": list(self.command),
            "preparation": [
                {
                    "argv": list(item.argv),
                    "returncode": item.returncode,
                    "stdout": item.stdout,
                    "stderr": item.stderr,
                    "duration_seconds": item.duration_seconds,
                }
                for item in self.preparation
            ],
        }


__all__ = ["ComparisonResult", "ComparisonStatus", "ComparatorRequest"]
