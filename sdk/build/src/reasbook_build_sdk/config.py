"""Environment and argument configuration for the build CLI/API."""

from __future__ import annotations

import math
import os
import re
from argparse import Namespace
from typing import Mapping, Sequence

from .errors import ConfigurationError
from .models import BuildOptions


def _env(name: str, environ: Mapping[str, str]) -> str | None:
    value = environ.get(name)
    if value is None:
        return None
    value = value.strip()
    return value or None


def _arg(args: Namespace | object | None, name: str) -> object | None:
    return getattr(args, name, None) if args is not None else None


def _value(
    args: object | None,
    arg_name: str,
    env_names: Sequence[str],
    environ: Mapping[str, str],
) -> str | None:
    candidate = _arg(args, arg_name)
    if candidate is not None and str(candidate).strip():
        return str(candidate).strip()
    for name in env_names:
        found = _env(name, environ)
        if found is not None:
            return found
    return None


def _bool(name: str, value: str | None, *, default: bool) -> bool:
    if value is None:
        return default
    normalized = value.strip().lower()
    if normalized in {"1", "true", "yes", "on"}:
        return True
    if normalized in {"0", "false", "no", "off"}:
        return False
    raise ConfigurationError(f"{name} must be true/false, got {value!r}")


def _float(
    name: str, value: str | None, *, default: float | None, minimum: float | None = None
) -> float | None:
    if value is None:
        result = default
    else:
        try:
            result = float(value)
        except ValueError as exc:
            raise ConfigurationError(f"{name} must be a number, got {value!r}") from exc
    if result is not None and not math.isfinite(result):
        raise ConfigurationError(f"{name} must be finite, got {result}")
    if result is not None and minimum is not None and result < minimum:
        raise ConfigurationError(f"{name} must be >= {minimum}, got {result}")
    return result


def _split_values(raw: str | None) -> list[str]:
    if not raw:
        return []
    return [item.strip() for item in re.split(r"[,\n]", raw) if item.strip()]


def _parse_env_values(raw_values: Sequence[str]) -> tuple[tuple[str, str], ...]:
    result: list[tuple[str, str]] = []
    for raw in raw_values:
        if "=" not in raw:
            raise ConfigurationError(
                f"build environment expects KEY=VALUE, got {raw!r}"
            )
        key, value = raw.split("=", 1)
        key = key.strip()
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", key):
            raise ConfigurationError(
                f"invalid build environment variable name: {key!r}"
            )
        if any(char in value for char in "\x00\r\n"):
            raise ConfigurationError(
                f"build environment value for {key} contains a control character"
            )
        result.append((key, value))
    return tuple(result)


def load_build_options(
    args: object | None = None,
    *,
    environ: Mapping[str, str] | None = None,
    targets: Sequence[str] = (),
) -> BuildOptions:
    """Resolve an argument namespace and ``REASBOOK_BUILD_*`` environment.

    Explicit arguments win over environment values.  The returned model is
    immutable and can safely be shared by a planner and an injected executor.
    """

    env = os.environ if environ is None else environ
    arg_targets = _arg(args, "targets") or _arg(args, "target") or ()
    if isinstance(arg_targets, str):
        arg_targets = [arg_targets]
    target_values = list(targets) + list(arg_targets)
    if not target_values:
        target_values = _split_values(_env("REASBOOK_BUILD_TARGETS", env))

    raw_lake_args = _arg(args, "lake_arg") or _arg(args, "lake_args")
    if raw_lake_args is None:
        lake_args = _split_values(_env("REASBOOK_BUILD_LAKE_ARGS", env))
    elif isinstance(raw_lake_args, str):
        lake_args = _split_values(raw_lake_args)
    else:
        lake_args = [str(value) for value in raw_lake_args]

    lake_bin = _value(args, "lake_bin", ("REASBOOK_BUILD_LAKE_BIN",), env) or "lake"
    skip_cache = bool(_arg(args, "skip_cache_get"))
    cache_raw = _value(args, "run_cache_get", ("REASBOOK_BUILD_CACHE_GET",), env)
    run_cache_get = (
        False if skip_cache else _bool("run_cache_get", cache_raw, default=True)
    )
    cache_timeout = _float(
        "cache_timeout_seconds",
        _value(args, "cache_timeout_seconds", ("REASBOOK_BUILD_CACHE_TIMEOUT",), env),
        default=1800.0,
        minimum=0.1,
    )
    build_timeout = _float(
        "build_timeout_seconds",
        _value(args, "build_timeout_seconds", ("REASBOOK_BUILD_TIMEOUT",), env),
        default=None,
        minimum=0.1,
    )
    no_verify = bool(_arg(args, "no_verify_outputs"))
    verify_raw = _value(args, "verify_outputs", ("REASBOOK_BUILD_VERIFY_OUTPUTS",), env)
    verify_outputs = (
        False if no_verify else _bool("verify_outputs", verify_raw, default=True)
    )

    raw_env = _arg(args, "build_env") or _arg(args, "env")
    if raw_env is None:
        raw_env = _split_values(_env("REASBOOK_BUILD_ENV", env))
    elif isinstance(raw_env, str):
        raw_env = [raw_env]
    environment = list(_parse_env_values(raw_env))
    # These two conventional cache variables are exposed as convenience flags;
    # callers can still pass any other variable through --env.
    for option_name, variable_name in (
        ("mathlib_cache_dir", "MATHLIB_CACHE_DIR"),
        ("xdg_cache_home", "XDG_CACHE_HOME"),
    ):
        value = _value(
            args, option_name, (f"REASBOOK_BUILD_{option_name.upper()}",), env
        )
        if value is not None and not any(
            key == variable_name for key, _ in environment
        ):
            environment.append((variable_name, value))

    raw_extensions = _value(
        args, "artifact_extensions", ("REASBOOK_BUILD_ARTIFACT_EXTENSIONS",), env
    )
    extensions = tuple(_split_values(raw_extensions)) if raw_extensions else (".olean",)
    return BuildOptions.from_values(
        targets=tuple(str(value) for value in target_values),
        lake_args=tuple(lake_args),
        lake_bin=lake_bin,
        run_cache_get=run_cache_get,
        cache_timeout_seconds=cache_timeout or 1800.0,
        build_timeout_seconds=build_timeout,
        environment=tuple(environment),
        verify_outputs=verify_outputs,
        artifact_extensions=extensions,
    )
