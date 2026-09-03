"""Build orchestration and executor extension points."""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Protocol

from reasbook_sdk_common import (
    CommandExecutionError,
    CommandResult,
    CommandTimeoutError,
)

from .command import CommandError, CommandRunner
from .executor import SubprocessRunner
from .lake import plan_build
from .models import BuildOptions, BuildPlan, BuildResult
from .project import LakeProject, discover_project, first_artifact


class PlanExecutor(Protocol):
    """Protocol for an object that executes a complete build plan."""

    def execute(self, plan: BuildPlan) -> BuildResult:
        """Execute ``plan`` and return the standard result model."""


# This name reads naturally for consumers and leaves room for other plan
# executor implementations without coupling the SDK to a particular backend.
BuildExecutor = PlanExecutor


@dataclass
class LocalBuildExecutor:
    """Execute every command in a plan sequentially in the project checkout."""

    runner: CommandRunner = field(default_factory=lambda: SubprocessRunner(stream=True))

    def execute(self, plan: BuildPlan) -> BuildResult:
        results: list[CommandResult] = []
        for command in plan.commands:
            try:
                result = self.runner.run(command)
            except CommandTimeoutError as exc:
                return BuildResult(
                    plan=plan,
                    status="timed_out",
                    command_results=tuple(results),
                    message=str(exc),
                )
            except (CommandExecutionError, CommandError) as exc:
                return BuildResult(
                    plan=plan,
                    status="failed",
                    command_results=tuple(results),
                    message=str(exc),
                )
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
            results.append(result)
            if result.timed_out:
                return BuildResult(
                    plan=plan,
                    status="timed_out",
                    command_results=tuple(results),
                    message=f"command timed out: {command.display}",
                )
            if not result.succeeded:
                return BuildResult(
                    plan=plan,
                    status="failed",
                    command_results=tuple(results),
                    message=(
                        f"command failed with exit code {result.returncode}: {command.display}"
                    ),
                )

        artifacts: tuple[Path, ...] = ()
        if plan.options.verify_outputs:
            artifact = first_artifact(plan.project, plan.options.artifact_extensions)
            if artifact is None:
                return BuildResult(
                    plan=plan,
                    status="failed",
                    command_results=tuple(results),
                    message=(
                        "build commands succeeded, but no expected artifact was found "
                        f"under {', '.join(str(root) for root in plan.project.build_roots)}"
                    ),
                )
            artifacts = (artifact,)
        return BuildResult(
            plan=plan,
            status="success",
            command_results=tuple(results),
            artifacts=artifacts,
        )


@dataclass
class DryRunExecutor:
    """Return a result without executing any command."""

    def execute(self, plan: BuildPlan) -> BuildResult:
        return BuildResult(plan=plan, status="dry_run", message=plan_summary(plan))


def plan_summary(plan: BuildPlan) -> str:
    return f"{len(plan.commands)} command(s) planned for {plan.project.root} ({plan.target_label})"


@dataclass
class BuildService:
    """High-level API used by scripts, web services, and the CLI."""

    executor: PlanExecutor = field(default_factory=LocalBuildExecutor)

    def discover(self, project_root: str | Path) -> LakeProject:
        return discover_project(project_root)

    def plan(
        self,
        project_root: str | Path,
        options: BuildOptions | None = None,
        **planning_kwargs: object,
    ) -> BuildPlan:
        project = self.discover(project_root)
        if options is None:
            # ``plan_build`` accepts the explicit keyword form; keeping this
            # forwarding narrow avoids a second options parser in the service.
            return plan_build(project, **planning_kwargs)  # type: ignore[arg-type]
        if planning_kwargs:
            raise TypeError("pass options or planning keywords, not both")
        return plan_build(project, options)

    def run(
        self,
        project_root: str | Path,
        options: BuildOptions | None = None,
        *,
        dry_run: bool = False,
        **planning_kwargs: object,
    ) -> BuildResult:
        plan = self.plan(project_root, options, **planning_kwargs)
        executor: PlanExecutor = DryRunExecutor() if dry_run else self.executor
        return executor.execute(plan)
