"""argv construction for Comparator preparation and execution."""

from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

from reasbook_sdk_common import Command

from .config import ComparatorConfig

if TYPE_CHECKING:
    from .models import ComparatorRequest


def _environment(config: ComparatorConfig) -> dict[str, str]:
    environment = config.environment_dict
    # Comparator-specific tool overrides are ordinary process variables.  The
    # caller can still provide them through ``environment`` when desired.
    if config.landrun_bin:
        environment["COMPARATOR_LANDRUN"] = config.landrun_bin
    if config.lean4export_bin:
        environment["COMPARATOR_LEAN4EXPORT"] = config.lean4export_bin
    if config.nanoda_bin:
        environment["COMPARATOR_NANODA"] = config.nanoda_bin
    environment.setdefault("LEAN_ABORT_ON_PANIC", "1")
    return environment


def cache_command(config: ComparatorConfig, root: Path, lake_bin: str) -> Command:
    """Build an optional Mathlib cache preflight command."""

    return Command(
        (lake_bin, "exe", "cache", "get"),
        cwd=root,
        env=_environment(config),
        timeout=config.cache_timeout_seconds,
    )


def build_command(config: ComparatorConfig) -> Command:
    """Build the Comparator executable and its exporter."""

    return Command(
        (config.effective_comparator_lake_bin, "build", "lean4export", "comparator"),
        cwd=config.comparator_root,
        env=_environment(config),
        timeout=config.timeout_seconds,
    )


def _sandboxed(argv: tuple[str, ...], config: ComparatorConfig) -> tuple[str, ...]:
    if config.sandbox_mode == "direct":
        return argv
    # Keep the wrapper argv-only too; no shell is needed for a Comparator
    # invocation and paths containing spaces remain unambiguous.
    return (
        "systemd-run",
        "--user",
        "--wait",
        "--collect",
        "--pipe",
        "--property=RestrictAddressFamilies=~AF_UNIX",
        "--working-directory",
        str(config.project_root),
        "--",
        *argv,
    )


def compare_command(config: ComparatorConfig) -> Command:
    """Build the command that asks Comparator to judge the solution."""

    argv = (
        config.lake_bin,
        "env",
        str(config.effective_comparator_bin),
        str(config.config_path),
    )
    return Command(
        _sandboxed(argv, config),
        cwd=config.project_root,
        env=_environment(config),
        timeout=config.timeout_seconds,
    )


def request_from_config(config: ComparatorConfig) -> "ComparatorRequest":
    """Create a complete immutable command plan."""

    # Import lazily to avoid a module cycle between models and commands.
    from .models import ComparatorRequest

    caches: list[Command] = []
    if config.cache_before_compare:
        caches.append(cache_command(config, config.project_root, config.lake_bin))
        if config.cache_comparator and config.comparator_root != config.project_root:
            caches.append(
                cache_command(
                    config, config.comparator_root, config.effective_comparator_lake_bin
                )
            )
    return ComparatorRequest(
        config=config,
        build_command=build_command(config) if config.build_comparator else None,
        compare_command=compare_command(config),
        cache_commands=tuple(caches),
    )


__all__ = ["build_command", "cache_command", "compare_command", "request_from_config"]
