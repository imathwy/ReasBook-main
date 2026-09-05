"""Safe argv construction for generator and Lake invocations."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Mapping

from reasbook_sdk_common import Command

from .config import LEAN_ENV_NAMES, VersoBuildConfig


@dataclass(frozen=True)
class CommandSpec:
    """One pipeline command and the directory in which it should run."""

    stage: str
    argv: tuple[str, ...]
    cwd: Path

    def public_dict(self) -> dict[str, object]:
        return {"stage": self.stage, "argv": list(self.argv), "cwd": str(self.cwd)}

    def to_command(self, *, environment: Mapping[str, str] = ()) -> Command:
        """Convert this staged plan item to the shared execution model."""

        return Command(self.argv, cwd=self.cwd, env=dict(environment))


def lake_argv(config: VersoBuildConfig, *args: str) -> tuple[str, ...]:
    """Build an argv vector, optionally pinning execution through Elan.

    When no explicit arguments are supplied, the configured target tuple is
    used.  This makes the helper convenient for callers while ``pipeline`` can
    still pass a different target list when needed.
    """

    if not args:
        args = config.targets

    if config.toolchain:
        install = ("--install",) if config.install_toolchain else ()
        return (
            config.elan_bin,
            "run",
            *install,
            config.toolchain,
            config.lake_bin,
            *args,
        )
    return (config.lake_bin, *args)


def pipeline(config: VersoBuildConfig) -> tuple[CommandSpec, ...]:
    """Return generator and Lake commands without executing them."""

    commands: list[CommandSpec] = []
    generator_cwd = config.generator_cwd or config.web_root
    if config.generator:
        commands.append(CommandSpec("generate", config.generator, generator_cwd))
    targets = config.targets
    if config.output_dir is not None:
        # ``Verso.Genre.Blog.blogMain`` accepts this option after the Lake
        # executable target.  Passing it explicitly is essential for
        # concurrent project finalizers: an environment variable alone is not
        # consumed by the generated Lean executable.
        targets = (*targets, "--output", str(config.output_dir))
    commands.append(CommandSpec("build", lake_argv(config, *targets), config.web_root))
    return tuple(commands)


def clean_environment(
    base: Mapping[str, str],
    config: VersoBuildConfig,
) -> dict[str, str]:
    """Apply explicit values and remove inherited Lake internals if requested."""

    environment = dict(base)
    if config.clean_lean_environment:
        for name in LEAN_ENV_NAMES:
            environment.pop(name, None)
    environment.update(config.environment)
    return environment


__all__ = ["CommandSpec", "clean_environment", "lake_argv", "pipeline"]
