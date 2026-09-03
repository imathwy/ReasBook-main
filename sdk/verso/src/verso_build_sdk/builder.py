"""High-level Verso build orchestration."""

from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

from reasbook_sdk_common import (
    CommandExecutionError as SharedCommandExecutionError,
    CommandTimeoutError,
)

from .commands import CommandSpec, clean_environment, pipeline
from .config import VersoBuildConfig
from .errors import CommandExecutionError, ProjectValidationError, VersoBuildError
from .project import VersoProject, discover_project
from .runner import CommandResult, CommandRunner, SubprocessRunner


@dataclass(frozen=True)
class VersoBuildResult:
    """Result of a completed or planned build."""

    project: VersoProject
    commands: tuple[CommandSpec, ...]
    results: tuple[CommandResult, ...] = ()
    dry_run: bool = False

    @property
    def output_dir(self) -> Path | None:
        return self._configured_output

    # Keep the configured output on the result without retaining the full
    # second config object; ``with_output`` populates it in the builder.
    _configured_output: Path | None = None

    def public_dict(self) -> dict[str, object]:
        return {
            "project_root": str(self.project.root),
            "commands": [command.public_dict() for command in self.commands],
            "return_codes": [result.returncode for result in self.results],
            "dry_run": self.dry_run,
            "output_dir": str(self.output_dir) if self.output_dir else None,
        }


class VersoBuilder:
    """Build a Verso project with explicit, testable pipeline stages."""

    def __init__(
        self,
        config: VersoBuildConfig,
        *,
        runner: CommandRunner | None = None,
        environ: dict[str, str] | None = None,
        project_discoverer: Callable[[Path], VersoProject] = discover_project,
    ) -> None:
        self.config = config
        self.runner = runner or SubprocessRunner()
        self.environ = environ if environ is not None else dict(os.environ)
        self.project_discoverer = project_discoverer
        self.project: VersoProject | None = None

    def discover(self) -> VersoProject:
        if self.project is None:
            self.project = self.project_discoverer(self.config.web_root)
        return self.project

    def resolved_config(self) -> VersoBuildConfig:
        project = self.discover()
        return self.config.resolved(project_toolchain=project.toolchain)

    def plan(self) -> tuple[CommandSpec, ...]:
        config = self.resolved_config()
        return pipeline(config)

    def run(self, *, dry_run: bool = False) -> VersoBuildResult:
        project = self.discover()
        config = self.config.resolved(project_toolchain=project.toolchain)
        commands = pipeline(config)
        if dry_run:
            return VersoBuildResult(project, commands, (), True, config.output_dir)

        environment = clean_environment(self.environ, config)
        results: list[CommandResult] = []
        for command in commands:
            if not command.cwd.is_dir():
                raise ProjectValidationError(
                    f"command working directory does not exist: {command.cwd}"
                )
            try:
                result = self.runner.run(command.to_command(environment=environment))
            except CommandTimeoutError as exc:
                raise CommandExecutionError(tuple(command.argv), 124, str(exc)) from exc
            except SharedCommandExecutionError as exc:
                raise CommandExecutionError(tuple(command.argv), 1, str(exc)) from exc
            if result.returncode != 0:
                raise CommandExecutionError(
                    tuple(command.argv),
                    result.returncode,
                    result.stderr,
                )
            results.append(result)

        if config.verify_output and config.output_dir is not None:
            if not config.output_dir.is_dir():
                raise VersoBuildError(
                    f"Verso build completed but output directory is missing: {config.output_dir}"
                )
        return VersoBuildResult(
            project, commands, tuple(results), False, config.output_dir
        )


__all__ = ["VersoBuildResult", "VersoBuilder"]
