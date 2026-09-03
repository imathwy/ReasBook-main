"""Lake-specific command planning.

This module knows how to turn a :class:`LakeProject` and generic
:class:`BuildOptions` into immutable commands.  It does not execute commands or
know how an executor transports them.
"""

from __future__ import annotations

import shlex
from pathlib import Path
from typing import Mapping, Sequence

from .command import Command
from .errors import ConfigurationError
from .models import BuildOptions, BuildPlan
from .project import LakeProject, discover_project


def _project(value: LakeProject | str | Path) -> LakeProject:
    return value if isinstance(value, LakeProject) else discover_project(value)


def _targets(values: Sequence[str]) -> tuple[str, ...]:
    result: list[str] = []
    seen: set[str] = set()
    for target in values:
        if not isinstance(target, str) or not target:
            raise ConfigurationError("Lake targets must be non-empty strings")
        if any(char in target for char in "\x00\r\n"):
            raise ConfigurationError(
                f"Lake target contains a control character: {target!r}"
            )
        if target not in seen:
            seen.add(target)
            result.append(target)
    return tuple(result)


def cache_command(
    project: LakeProject | str | Path,
    *,
    lake_bin: str = "lake",
    timeout_seconds: float = 1800.0,
    lake_args: Sequence[str] = (),
    targets: Sequence[str] = (),
    environment: Mapping[str, str] | Sequence[tuple[str, str]] = (),
) -> Command:
    """Plan the optional local cache preflight command."""

    metadata = _project(project)
    return Command(
        argv=(lake_bin, *tuple(lake_args), "exe", "cache", "get", *tuple(targets)),
        cwd=metadata.root,
        env=tuple(environment.items())
        if isinstance(environment, Mapping)
        else tuple(environment),
        timeout=timeout_seconds,
    )


def build_command(
    project: LakeProject | str | Path,
    targets: Sequence[str] = (),
    *,
    lake_bin: str = "lake",
    timeout_seconds: float | None = None,
    lake_args: Sequence[str] = (),
    environment: Mapping[str, str] | Sequence[tuple[str, str]] = (),
) -> Command:
    """Plan a ``lake build`` command for one project."""

    metadata = _project(project)
    normalized_targets = _targets(targets)
    return Command(
        argv=(lake_bin, *tuple(lake_args), "build", *normalized_targets),
        cwd=metadata.root,
        env=tuple(environment.items())
        if isinstance(environment, Mapping)
        else tuple(environment),
        timeout=timeout_seconds,
    )


def plan_build(
    project: LakeProject | str | Path,
    options: BuildOptions | None = None,
    *,
    targets: Sequence[str] = (),
    lake_bin: str = "lake",
    run_cache_get: bool = True,
    cache_timeout_seconds: float = 1800.0,
    build_timeout_seconds: float | None = None,
    environment: Mapping[str, str] | Sequence[tuple[str, str]] = (),
    verify_outputs: bool = True,
    artifact_extensions: Sequence[str] = (".olean",),
    lake_args: Sequence[str] = (),
) -> BuildPlan:
    """Create an immutable plan, accepting either options or explicit values.

    Passing ``options`` is preferred for application code.  The keyword form
    keeps the function pleasant to use from small scripts and mirrors the CLI.
    """

    metadata = _project(project)
    if options is None:
        options = BuildOptions.from_values(
            targets=targets,
            lake_bin=lake_bin,
            run_cache_get=run_cache_get,
            cache_timeout_seconds=cache_timeout_seconds,
            build_timeout_seconds=build_timeout_seconds,
            environment=environment,
            verify_outputs=verify_outputs,
            artifact_extensions=artifact_extensions,
            lake_args=lake_args,
        )
    elif (
        targets
        or lake_bin != "lake"
        or run_cache_get is not True
        or cache_timeout_seconds != 1800.0
        or build_timeout_seconds is not None
        or environment
        or verify_outputs is not True
        or tuple(artifact_extensions) != (".olean",)
        or tuple(lake_args)
    ):
        raise ConfigurationError(
            "pass either options or explicit planning keywords, not both"
        )

    commands: list[Command] = []
    if options.run_cache_get:
        commands.append(
            cache_command(
                metadata,
                lake_bin=options.lake_bin,
                timeout_seconds=options.cache_timeout_seconds,
                environment=options.environment,
                lake_args=options.lake_args,
            )
        )
    commands.append(
        build_command(
            metadata,
            options.targets,
            lake_bin=options.lake_bin,
            timeout_seconds=options.build_timeout_seconds,
            environment=options.environment,
            lake_args=options.lake_args,
        )
    )
    return BuildPlan(project=metadata, options=options, commands=tuple(commands))


def shell_preview(plan: BuildPlan) -> str:
    """Render a safe, human-readable shell preview of a plan.

    The preview is for display only; executors should use ``Command.argv``.
    """

    rendered = [f"cd -- {shlex.quote(str(plan.project.root))}"]
    for command in plan.commands:
        # Keep values out of logs: callers commonly use this preview while
        # diagnosing a build with tokens or private cache paths in the env.
        env_prefix = " ".join(f"{shlex.quote(key)}=<set>" for key, _ in command.env)
        invocation = command.display
        rendered.append(f"{env_prefix} {invocation}".strip())
    return " && ".join(rendered)
