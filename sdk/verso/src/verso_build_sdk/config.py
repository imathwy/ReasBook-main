"""Configuration models for a reproducible, platform-neutral Verso build."""

from __future__ import annotations

import os
import re
import shlex
from dataclasses import dataclass, field
from pathlib import Path
from typing import Mapping

from .errors import VersoBuildError


LEAN_ENV_NAMES = (
    "LAKE",
    "LAKE_HOME",
    "LAKE_PKG_URL_MAP",
    "LEAN_SYSROOT",
    "LEAN_AR",
    "LEAN_PATH",
    "LEAN_SRC_PATH",
    "LEAN_GITHASH",
    "ELAN_TOOLCHAIN",
    "DYLD_LIBRARY_PATH",
    "LD_LIBRARY_PATH",
)


def _split_words(value: str | None) -> tuple[str, ...]:
    if value is None or not value.strip():
        return ()
    try:
        words = tuple(shlex.split(value))
    except ValueError as exc:
        raise VersoBuildError(f"invalid command syntax: {value!r}") from exc
    if any(not word or any(char in word for char in "\x00\r\n") for word in words):
        raise VersoBuildError(
            "commands may not contain empty/control-character arguments"
        )
    return words


def _bool_env(environ: Mapping[str, str], name: str, default: bool) -> bool:
    value = environ.get(name)
    if value is None or not value.strip():
        return default
    normalized = value.strip().lower()
    if normalized in {"1", "true", "yes", "on"}:
        return True
    if normalized in {"0", "false", "no", "off"}:
        return False
    raise VersoBuildError(f"{name} must be true or false, got {value!r}")


def _path(value: str | Path | None, *, base: Path | None = None) -> Path | None:
    if value is None:
        return None
    path = Path(value).expanduser()
    if not path.is_absolute() and base is not None:
        path = base / path
    return path.resolve()


@dataclass(frozen=True)
class VersoBuildConfig:
    """All inputs needed to run one Verso site build.

    ``generator`` is an optional argv tuple (for example ``("python",
    "scripts/gen_sections.py")``).  ``targets`` are passed verbatim after
    ``lake``; the default is the ReasBook site's executable target but callers
    can use the same SDK for any Verso project.
    """

    web_root: Path
    toolchain: str | None = None
    lake_bin: str = "lake"
    elan_bin: str = "elan"
    targets: tuple[str, ...] = ("exe", "reasbook-site")
    generator: tuple[str, ...] = ()
    generator_cwd: Path | None = None
    output_dir: Path | None = None
    install_toolchain: bool = True
    clean_lean_environment: bool = True
    verify_output: bool = False
    environment: tuple[tuple[str, str], ...] = field(default_factory=tuple)

    @classmethod
    def from_env(
        cls,
        web_root: Path,
        *,
        environ: Mapping[str, str] | None = None,
    ) -> "VersoBuildConfig":
        """Load optional ``VERSO_*`` settings without platform credentials."""

        env = environ if environ is not None else os.environ
        root = Path(web_root).expanduser().resolve()
        targets = _split_words(env.get("VERSO_TARGETS")) or cls.targets
        generator = _split_words(env.get("VERSO_GENERATOR"))
        configured: dict[str, str] = {}
        prefix = "VERSO_ENV_"
        for key, value in env.items():
            if key.startswith(prefix):
                configured[key[len(prefix) :]] = value
        return cls(
            web_root=Path(web_root),
            toolchain=env.get("VERSO_TOOLCHAIN") or None,
            lake_bin=env.get("VERSO_LAKE_BIN") or "lake",
            elan_bin=env.get("VERSO_ELAN_BIN") or "elan",
            targets=targets,
            generator=generator,
            generator_cwd=_path(env.get("VERSO_GENERATOR_CWD"), base=root),
            output_dir=_path(env.get("VERSO_OUTPUT_DIR"), base=root),
            install_toolchain=_bool_env(env, "VERSO_INSTALL_TOOLCHAIN", True),
            clean_lean_environment=_bool_env(env, "VERSO_CLEAN_LEAN_ENV", True),
            verify_output=_bool_env(env, "VERSO_VERIFY_OUTPUT", False),
            environment=tuple(sorted(configured.items())),
        )

    def resolved(self, *, project_toolchain: str | None = None) -> "VersoBuildConfig":
        """Return a normalized copy, filling the toolchain from the project."""

        root = Path(self.web_root).expanduser().resolve()
        toolchain = self.toolchain or project_toolchain
        generator_cwd = _path(self.generator_cwd, base=root)
        output_dir = _path(self.output_dir, base=root)
        config = self.__class__(
            web_root=root,
            toolchain=toolchain.strip() if toolchain else None,
            lake_bin=self.lake_bin,
            elan_bin=self.elan_bin,
            targets=tuple(self.targets),
            generator=tuple(self.generator),
            generator_cwd=generator_cwd,
            output_dir=output_dir,
            install_toolchain=self.install_toolchain,
            clean_lean_environment=self.clean_lean_environment,
            verify_output=self.verify_output,
            environment=tuple(self.environment),
        )
        config.validate()
        return config

    def validate(self) -> None:
        if not self.web_root.is_absolute():
            raise VersoBuildError(
                f"web_root must be absolute after resolution: {self.web_root}"
            )
        if not self.lake_bin or not self.elan_bin:
            raise VersoBuildError("lake_bin and elan_bin must be non-empty")
        if not self.targets:
            raise VersoBuildError("at least one Lake target is required")
        if self.output_dir is not None:
            if (
                len(self.targets) < 2
                or self.targets[0] != "exe"
                or not self.targets[1]
                or self.targets[1].startswith("-")
            ):
                raise VersoBuildError(
                    "output_dir requires targets to start with 'exe' and an "
                    "executable name"
                )
            if "--output" in self.targets:
                raise VersoBuildError(
                    "output_dir may not be combined with an explicit --output target"
                )
        for value in (*self.targets, *self.generator, self.lake_bin, self.elan_bin):
            if any(char in value for char in "\x00\r\n"):
                raise VersoBuildError(
                    "command arguments may not contain control characters"
                )
        if self.toolchain and any(char in self.toolchain for char in "\x00\r\n"):
            raise VersoBuildError("toolchain may not contain control characters")
        for key, value in self.environment:
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", key):
                raise VersoBuildError(f"invalid environment key: {key!r}")
            if any(char in value for char in "\x00\r\n"):
                raise VersoBuildError(
                    f"environment value for {key!r} contains a control character"
                )

    def public_dict(self) -> dict[str, object]:
        """Serialize configuration for logs/dry-runs (without hidden values)."""

        return {
            "web_root": str(self.web_root),
            "toolchain": self.toolchain,
            "lake_bin": self.lake_bin,
            "elan_bin": self.elan_bin,
            "targets": list(self.targets),
            "generator": list(self.generator),
            "generator_cwd": str(self.generator_cwd) if self.generator_cwd else None,
            "output_dir": str(self.output_dir) if self.output_dir else None,
            "install_toolchain": self.install_toolchain,
            "clean_lean_environment": self.clean_lean_environment,
            "verify_output": self.verify_output,
            "environment_keys": [key for key, _ in self.environment],
        }


__all__ = ["LEAN_ENV_NAMES", "VersoBuildConfig"]
