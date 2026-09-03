"""Public data models shared by planning, execution, and integrations."""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal, Mapping, Sequence

from .command import Command, CommandResult, _normalize_env
from .errors import ConfigurationError
from .project import LakeProject


def _unique_strings(values: Sequence[str]) -> tuple[str, ...]:
    result: list[str] = []
    seen: set[str] = set()
    for value in values:
        if not isinstance(value, str) or not value:
            raise ConfigurationError("build targets must be non-empty strings")
        if any(char in value for char in "\x00\r\n"):
            raise ConfigurationError(
                f"build target contains a control character: {value!r}"
            )
        if value not in seen:
            seen.add(value)
            result.append(value)
    return tuple(result)


@dataclass(frozen=True)
class BuildOptions:
    """Options that affect a planned Lake build.

    The model intentionally contains only build concerns.  Authentication,
    scheduling, container images, and other deployment details belong to an
    injected executor in the application using this package.
    """

    targets: tuple[str, ...] = ()
    lake_args: tuple[str, ...] = ()
    lake_bin: str = "lake"
    run_cache_get: bool = True
    cache_timeout_seconds: float = 1800.0
    build_timeout_seconds: float | None = None
    environment: tuple[tuple[str, str], ...] = field(default_factory=tuple)
    verify_outputs: bool = True
    artifact_extensions: tuple[str, ...] = (".olean",)

    def __post_init__(self) -> None:
        object.__setattr__(self, "targets", _unique_strings(self.targets))
        object.__setattr__(self, "lake_args", _unique_strings(self.lake_args))
        if not isinstance(self.lake_bin, str) or not self.lake_bin.strip():
            raise ConfigurationError("lake_bin must be a non-empty string")
        if any(char in self.lake_bin for char in "\x00\r\n"):
            raise ConfigurationError("lake_bin contains a control character")
        if (
            not math.isfinite(self.cache_timeout_seconds)
            or self.cache_timeout_seconds <= 0
        ):
            raise ConfigurationError("cache_timeout_seconds must be positive")
        if self.build_timeout_seconds is not None and (
            not math.isfinite(self.build_timeout_seconds)
            or self.build_timeout_seconds <= 0
        ):
            raise ConfigurationError("build_timeout_seconds must be positive")
        try:
            normalized_environment = _normalize_env(self.environment)
        except ValueError as exc:
            raise ConfigurationError(str(exc)) from exc
        object.__setattr__(self, "environment", normalized_environment)
        extensions = tuple(
            extension if extension.startswith(".") else f".{extension}"
            for extension in self.artifact_extensions
        )
        if not extensions or any(
            not extension or any(char in extension for char in "\x00\r\n")
            for extension in extensions
        ):
            raise ConfigurationError(
                "artifact_extensions must contain safe non-empty values"
            )
        object.__setattr__(self, "artifact_extensions", extensions)

    @classmethod
    def from_values(
        cls,
        *,
        targets: Sequence[str] = (),
        lake_args: Sequence[str] = (),
        lake_bin: str = "lake",
        run_cache_get: bool = True,
        cache_timeout_seconds: float = 1800.0,
        build_timeout_seconds: float | None = None,
        environment: Mapping[str, str] | Sequence[tuple[str, str]] = (),
        verify_outputs: bool = True,
        artifact_extensions: Sequence[str] = (".olean",),
    ) -> "BuildOptions":
        """Convenience constructor accepting ordinary mappings/lists."""

        return cls(
            targets=tuple(targets),
            lake_args=tuple(lake_args),
            lake_bin=lake_bin,
            run_cache_get=run_cache_get,
            cache_timeout_seconds=cache_timeout_seconds,
            build_timeout_seconds=build_timeout_seconds,
            environment=tuple(environment.items())
            if isinstance(environment, Mapping)
            else tuple(environment),
            verify_outputs=verify_outputs,
            artifact_extensions=tuple(artifact_extensions),
        )


@dataclass(frozen=True)
class BuildPlan:
    """Immutable build plan that an executor can serialize or execute."""

    project: LakeProject
    options: BuildOptions
    commands: tuple[Command, ...]

    @property
    def target_label(self) -> str:
        return (
            ", ".join(self.options.targets)
            if self.options.targets
            else "default target"
        )

    @property
    def command_previews(self) -> tuple[str, ...]:
        return tuple(command.display for command in self.commands)

    def public_dict(self) -> dict[str, object]:
        """Return a deterministic plan description without environment values."""

        return {
            "project": str(self.project.root),
            "toolchain": self.project.toolchain,
            "package": self.project.package_name,
            "targets": list(self.options.targets),
            "lake_args": list(self.options.lake_args),
            "commands": [
                {
                    "argv": list(command.argv),
                    "cwd": str(command.cwd) if command.cwd is not None else None,
                    "timeout_seconds": command.timeout_seconds,
                    "environment_keys": [key for key, _ in command.env],
                }
                for command in self.commands
            ],
        }


BuildStatus = Literal["success", "failed", "timed_out", "dry_run"]


@dataclass(frozen=True)
class BuildResult:
    """Stable result shape returned by every executor integration."""

    plan: BuildPlan
    status: BuildStatus
    command_results: tuple[CommandResult, ...] = ()
    artifacts: tuple[Path, ...] = ()
    message: str = ""

    @property
    def succeeded(self) -> bool:
        return self.status == "success"

    @property
    def failed(self) -> bool:
        return self.status in {"failed", "timed_out"}

    def summary(self) -> str:
        if self.message:
            return self.message
        if self.status == "dry_run":
            return f"dry run: {len(self.plan.commands)} command(s) planned"
        if self.succeeded:
            return f"build succeeded ({len(self.artifacts)} artifact(s) detected)"
        return f"build {self.status}"

    def public_dict(self) -> dict[str, object]:
        """Return a JSON-friendly result with no environment values."""

        return {
            "status": self.status,
            "succeeded": self.succeeded,
            "project": str(self.plan.project.root),
            "targets": list(self.plan.options.targets),
            "artifacts": [str(path) for path in self.artifacts],
            "commands": [
                {
                    "argv": list(snapshot.argv),
                    "returncode": snapshot.returncode,
                    "timed_out": snapshot.timed_out,
                    "duration_seconds": round(snapshot.duration_seconds, 3),
                }
                for snapshot in self.command_results
            ],
            "message": self.summary(),
        }
