"""Runtime options and JSON validation for Lean Comparator."""

from __future__ import annotations

import json
import math
import os
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Mapping, Sequence

from reasbook_sdk_common import ensure_absolute

from .errors import ComparatorConfigError
from .project import discover_comparator_root, discover_project, resolve_config_path


_ENV_KEY = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


def _safe_text(value: str, *, field_name: str) -> str:
    if any(char in value for char in "\x00\r\n"):
        raise ComparatorConfigError(f"{field_name} contains a control character")
    return value


def _command(value: str | Path, *, field_name: str) -> str:
    text = _safe_text(str(value).strip(), field_name=field_name)
    if not text:
        raise ComparatorConfigError(f"{field_name} must not be empty")
    if any(char.isspace() for char in text) and not text.startswith("/"):
        raise ComparatorConfigError(
            f"{field_name} must be a command name or executable path"
        )
    return text


def _module_name(value: Any, *, field_name: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ComparatorConfigError(f"{field_name} must be a non-empty string")
    value = value.strip()
    if any(char in value for char in "\x00\r\n/\\"):
        raise ComparatorConfigError(f"{field_name} contains an unsafe character")
    # Lean permits quoted identifiers; a lightweight structural check catches
    # path traversal without imposing ASCII-only names.
    if value in {".", ".."} or ".." in value.split("."):
        raise ComparatorConfigError(f"{field_name} contains an unsafe component")
    return value


def _name_array(
    value: Any,
    *,
    field_name: str,
    required: bool = True,
    allow_empty: bool = False,
) -> tuple[str, ...]:
    if value is None and not required:
        return ()
    if not isinstance(value, list):
        raise ComparatorConfigError(f"{field_name} must be an array")
    if required and not value and not allow_empty:
        raise ComparatorConfigError(f"{field_name} must not be empty")
    values: list[str] = []
    for item in value:
        values.append(_module_name(item, field_name=field_name))
    return tuple(values)


def validate_comparator_data(data: Any) -> dict[str, Any]:
    """Validate the shape consumed by Comparator and return the object."""

    if not isinstance(data, dict):
        raise ComparatorConfigError("Comparator configuration must be a JSON object")
    for field_name in ("challenge_module", "solution_module"):
        _module_name(data.get(field_name), field_name=field_name)
    _name_array(data.get("theorem_names"), field_name="theorem_names")
    _name_array(
        data.get("definition_names"), field_name="definition_names", required=False
    )
    _name_array(
        data.get("permitted_axioms"), field_name="permitted_axioms", allow_empty=True
    )
    enable_nanoda = data.get("enable_nanoda")
    if enable_nanoda is not None and not isinstance(enable_nanoda, bool):
        raise ComparatorConfigError("enable_nanoda must be boolean")
    external = data.get("external_kernels")
    if external is not None:
        if not isinstance(external, dict):
            raise ComparatorConfigError("external_kernels must be an object")
        for name, argv in external.items():
            _module_name(name, field_name="external kernel name")
            if (
                not isinstance(argv, list)
                or not argv
                or any(not isinstance(item, str) or not item for item in argv)
            ):
                raise ComparatorConfigError(
                    f"external kernel {name!r} must have a non-empty command array"
                )
            if any(any(char in item for char in "\x00\r\n") for item in argv):
                raise ComparatorConfigError(
                    f"external kernel {name!r} contains a control character"
                )
    return data


def validate_comparator_json(path: str | Path) -> dict[str, Any]:
    """Read and validate a Comparator JSON configuration."""

    path = Path(path)
    try:
        payload = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise ComparatorConfigError(
            f"cannot read Comparator config {path}: {exc}"
        ) from exc
    try:
        data = json.loads(payload)
    except json.JSONDecodeError as exc:
        raise ComparatorConfigError(
            f"invalid JSON in Comparator config {path}: {exc}"
        ) from exc
    return validate_comparator_data(data)


def _parse_environment(
    values: Mapping[str, str] | Sequence[tuple[str, str]] | None,
) -> tuple[tuple[str, str], ...]:
    if values is None:
        return ()
    items = values.items() if isinstance(values, Mapping) else values
    parsed: list[tuple[str, str]] = []
    for key, value in items:
        key = str(key)
        value = str(value)
        if not _ENV_KEY.fullmatch(key):
            raise ComparatorConfigError(f"invalid environment variable name: {key!r}")
        _safe_text(value, field_name=f"environment value for {key}")
        parsed.append((key, value))
    return tuple(sorted(parsed))


@dataclass(frozen=True)
class ComparatorConfig:
    """All inputs needed for one local Comparator invocation."""

    project_root: Path
    config_path: Path
    comparator_root: Path
    lake_bin: str = "lake"
    comparator_lake_bin: str | None = None
    comparator_bin: Path | None = None
    landrun_bin: str | None = None
    lean4export_bin: str | None = None
    nanoda_bin: str | None = None
    build_comparator: bool = True
    cache_before_compare: bool = False
    cache_comparator: bool = False
    timeout_seconds: float = 7200.0
    cache_timeout_seconds: float = 1800.0
    sandbox_mode: str = "direct"
    environment: tuple[tuple[str, str], ...] = field(default_factory=tuple)
    verify_outputs: bool = False
    lock: bool = True
    result_file: Path | None = None

    @classmethod
    def from_paths(
        cls,
        project_root: str | Path,
        config_path: str | Path,
        comparator_root: str | Path,
        **kwargs: Any,
    ) -> "ComparatorConfig":
        """Construct a normalized config after validating all project paths."""

        project = discover_project(project_root)
        comparator = discover_comparator_root(comparator_root)
        config = resolve_config_path(project.root, config_path)
        validate_comparator_json(config)
        values = dict(kwargs)
        for name in (
            "lake_bin",
            "comparator_lake_bin",
            "landrun_bin",
            "lean4export_bin",
            "nanoda_bin",
        ):
            if values.get(name) is not None:
                values[name] = _command(values[name], field_name=name)
        if values.get("comparator_bin") is not None:
            try:
                comparator_bin = Path(values["comparator_bin"])
                if not comparator_bin.is_absolute():
                    comparator_bin = comparator.root / comparator_bin
                values["comparator_bin"] = ensure_absolute(
                    comparator_bin, field="comparator_bin"
                )
            except ValueError as exc:
                raise ComparatorConfigError(str(exc)) from exc
        if values.get("result_file") is not None:
            try:
                values["result_file"] = ensure_absolute(
                    values["result_file"], field="result_file"
                )
            except ValueError as exc:
                raise ComparatorConfigError(str(exc)) from exc
        if "environment" in values:
            values["environment"] = _parse_environment(values["environment"])
        normalized = cls(
            project_root=project.root,
            config_path=config,
            comparator_root=comparator.root,
            **values,
        )
        normalized.validate()
        return normalized

    @classmethod
    def from_env(
        cls,
        project_root: str | Path,
        config_path: str | Path,
        comparator_root: str | Path,
        *,
        environ: Mapping[str, str] | None = None,
        **overrides: Any,
    ) -> "ComparatorConfig":
        """Load optional `COMPARATOR_*` values for local invocations."""

        env = environ if environ is not None else os.environ
        env_names = {
            "build_comparator": ("COMPARATOR_BUILD_COMPARATOR", "COMPARATOR_BUILD"),
            "cache_before_compare": (
                "COMPARATOR_CACHE_BEFORE_COMPARE",
                "COMPARATOR_CACHE",
            ),
            "cache_comparator": ("COMPARATOR_CACHE_COMPARATOR",),
            "verify_outputs": ("COMPARATOR_VERIFY_OUTPUTS",),
            "lock": ("COMPARATOR_LOCK",),
            "lake_bin": ("COMPARATOR_LAKE_BIN",),
            "comparator_lake_bin": ("COMPARATOR_COMPARATOR_LAKE_BIN",),
            "comparator_bin": ("COMPARATOR_BIN", "COMPARATOR_COMPARATOR_BIN"),
            "landrun_bin": ("COMPARATOR_LANDRUN_BIN", "COMPARATOR_LANDRUN"),
            "lean4export_bin": ("COMPARATOR_LEAN4EXPORT_BIN", "COMPARATOR_LEAN4EXPORT"),
            "nanoda_bin": ("COMPARATOR_NANODA_BIN", "COMPARATOR_NANODA"),
            "sandbox_mode": ("COMPARATOR_SANDBOX_MODE",),
            "result_file": ("COMPARATOR_RESULT_FILE",),
            "timeout_seconds": ("COMPARATOR_TIMEOUT_SECONDS",),
            "cache_timeout_seconds": ("COMPARATOR_CACHE_TIMEOUT_SECONDS",),
        }

        def value(name: str, default: Any = None) -> Any:
            if name in overrides:
                return overrides[name]
            for env_name in env_names.get(name, (name,)):
                if env_name in env:
                    return env[env_name]
            return default

        bool_names = {
            "build_comparator": True,
            "cache_before_compare": False,
            "cache_comparator": False,
            "verify_outputs": False,
            "lock": True,
        }
        parsed: dict[str, Any] = {}
        for name, default in bool_names.items():
            raw = value(name, default)
            if isinstance(raw, bool):
                parsed[name] = raw
            elif str(raw).strip().lower() in {"1", "true", "yes", "on"}:
                parsed[name] = True
            elif str(raw).strip().lower() in {"0", "false", "no", "off"}:
                parsed[name] = False
            else:
                raise ComparatorConfigError(
                    f"{env_names[name][0]} must be true or false"
                )
        for name in (
            "lake_bin",
            "comparator_lake_bin",
            "comparator_bin",
            "landrun_bin",
            "lean4export_bin",
            "nanoda_bin",
            "sandbox_mode",
            "result_file",
        ):
            raw = value(name)
            if raw is not None:
                parsed[name] = raw
        for name, default in (
            ("timeout_seconds", 7200.0),
            ("cache_timeout_seconds", 1800.0),
        ):
            raw = value(name, default)
            try:
                parsed[name] = float(raw)
            except (TypeError, ValueError) as exc:
                raise ComparatorConfigError(
                    f"{env_names[name][0]} must be a number"
                ) from exc
        configured_env = {
            key[len("COMPARATOR_ENV_") :]: val
            for key, val in env.items()
            if key.startswith("COMPARATOR_ENV_")
        }
        explicit_environment = overrides.get("environment")
        if explicit_environment is None:
            parsed["environment"] = configured_env
        else:
            merged_environment = dict(configured_env)
            merged_environment.update(dict(explicit_environment))
            parsed["environment"] = merged_environment
        return cls.from_paths(project_root, config_path, comparator_root, **parsed)

    def validate(self) -> None:
        """Validate runtime values that are independent of file discovery."""

        if (
            not self.project_root.is_absolute()
            or not self.comparator_root.is_absolute()
        ):
            raise ComparatorConfigError(
                "project_root and comparator_root must be absolute"
            )
        if not self.config_path.is_file():
            raise ComparatorConfigError(
                f"Comparator config does not exist: {self.config_path}"
            )
        if self.comparator_bin is not None and not self.comparator_bin.is_absolute():
            raise ComparatorConfigError("comparator_bin must be absolute")
        if (
            not math.isfinite(self.timeout_seconds)
            or not math.isfinite(self.cache_timeout_seconds)
            or self.timeout_seconds <= 0
            or self.cache_timeout_seconds <= 0
        ):
            raise ComparatorConfigError("timeouts must be positive")
        if self.sandbox_mode not in {"direct", "systemd"}:
            raise ComparatorConfigError("sandbox_mode must be 'direct' or 'systemd'")
        _parse_environment(self.environment)

    @property
    def effective_comparator_bin(self) -> Path:
        return (
            self.comparator_bin
            or self.comparator_root / ".lake" / "build" / "bin" / "comparator"
        )

    @property
    def effective_comparator_lake_bin(self) -> str:
        return self.comparator_lake_bin or self.lake_bin

    @property
    def environment_dict(self) -> dict[str, str]:
        return dict(self.environment)

    def public_dict(self) -> dict[str, Any]:
        """Return a diagnostics-safe representation without environment values."""

        return {
            "project_root": str(self.project_root),
            "config_path": str(self.config_path),
            "comparator_root": str(self.comparator_root),
            "lake_bin": self.lake_bin,
            "comparator_lake_bin": self.comparator_lake_bin,
            "comparator_bin": str(self.effective_comparator_bin),
            "build_comparator": self.build_comparator,
            "cache_before_compare": self.cache_before_compare,
            "cache_comparator": self.cache_comparator,
            "timeout_seconds": self.timeout_seconds,
            "sandbox_mode": self.sandbox_mode,
            "verify_outputs": self.verify_outputs,
            "environment_keys": [key for key, _ in self.environment],
        }


__all__ = [
    "ComparatorConfig",
    "validate_comparator_data",
    "validate_comparator_json",
]
