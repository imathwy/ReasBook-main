"""Runtime, cache, and command adapters used by the deploy orchestrator."""

from __future__ import annotations

from contextlib import contextmanager
import fcntl
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from typing import Iterator, Mapping, Protocol, Sequence

from reasbook_sdk_common import (
    Command,
    CommandExecutionError,
    CommandResult,
    CommandRunner,
    CommandTimeoutError,
    atomic_write_json,
)

from .errors import DeployExecutionError


# The local ReasBook deployment and SiFlow jobs share this external cache.
# Callers and CI runners may override it explicitly with REASBOOK_CACHE_ROOT.
DEFAULT_CACHE_ROOT = Path(
    "/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook"
)


class Runner(Protocol):
    """Minimal process port shared by deployment adapters and tests."""

    def run(self, command: Command) -> CommandResult:
        ...


def safe_name(value: str) -> str:
    """Convert an externally supplied label to a stable directory component."""

    return re.sub(r"[^A-Za-z0-9._-]+", "_", value)


def resolve_path(value: str | Path, base: str | Path | None = None) -> Path:
    """Resolve a user path without executing or creating it."""

    if any(char in str(value) for char in "\x00\r\n"):
        raise DeployExecutionError("path contains a control character")
    path = Path(value).expanduser()
    if not path.is_absolute():
        path = Path.cwd() / path if base is None else Path(base).expanduser() / path
    return path.resolve(strict=False)


def default_cache_root(*, environ: Mapping[str, str] | None = None) -> Path:
    """Return the fixed local cache root, honoring an explicit override."""

    env = os.environ if environ is None else environ
    configured = env.get("REASBOOK_CACHE_ROOT", "").strip()
    if configured:
        return resolve_path(configured)
    return DEFAULT_CACHE_ROOT


def read_env_defaults(path: Path) -> dict[str, str]:
    """Read simple ``KEY=value`` defaults without sourcing executable code."""

    values: dict[str, str] = {}
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return values
    for line in lines:
        stripped = line.strip()
        if not stripped or stripped.startswith("#") or "=" not in stripped:
            continue
        key, value = stripped.split("=", 1)
        key = key.strip()
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", key):
            continue
        value = value.strip()
        if len(value) >= 2 and value[0] == value[-1] and value[0] in {"'", '"'}:
            value = value[1:-1]
        values.setdefault(key, value)
    return values


def timeout_from_env(name: str, default: float, *, environ: Mapping[str, str] | None = None) -> float:
    """Parse a positive timeout from an environment mapping."""

    env = os.environ if environ is None else environ
    raw = env.get(name, str(default)).strip()
    try:
        value = float(raw)
    except ValueError:
        raise DeployExecutionError(f"{name} must be a positive number of seconds") from None
    if not math.isfinite(value) or value <= 0:
        raise DeployExecutionError(f"{name} must be a positive number of seconds")
    return value


def _result_for_dry_run(command: Command) -> CommandResult:
    return CommandResult(argv=command.argv, command=command)


def run_command(
    argv: Sequence[str],
    *,
    runner: Runner | None = None,
    cwd: Path | None = None,
    env: Mapping[str, str] | Sequence[tuple[str, str]] = (),
    timeout: float | None = None,
    input_text: str | None = None,
    log_path: Path | None = None,
    check: bool = True,
    dry_run: bool = False,
    label: str = "deploy",
) -> CommandResult:
    """Run one argv command through the shared command port.

    The deploy layer adds only logging and error translation; argument
    validation, environment normalization, and subprocess execution remain in
    ``sdk/common``.
    """

    command = Command(
        tuple(argv), cwd=cwd, env=env, timeout=timeout, input_text=input_text
    )
    print(f"[{label}] $ {command.display}")
    if dry_run:
        return _result_for_dry_run(command)
    direct_log = runner is None and log_path is not None
    if direct_log:
        log_path.parent.mkdir(parents=True, exist_ok=True)
    process_runner = runner or CommandRunner(
        stream=False,
        output_file=log_path if direct_log else None,
    )
    try:
        result = process_runner.run(command)
    except (CommandTimeoutError, CommandExecutionError) as exc:
        location = f"; log: {log_path}" if log_path else ""
        raise DeployExecutionError(f"{exc}{location}") from exc
    except Exception as exc:
        location = f"; log: {log_path}" if log_path else ""
        raise DeployExecutionError(f"command runner failed: {exc}{location}") from exc
    if log_path is not None and not direct_log:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        log_path.write_text(
            (result.stdout or "") + (result.stderr or ""),
            encoding="utf-8",
        )
    elif result.stdout:
        print(result.stdout, end="")
    if check and result.returncode != 0:
        if direct_log and log_path.is_file():
            output = log_path.read_text(encoding="utf-8", errors="replace")
        else:
            output = (result.stdout or "") + (result.stderr or "")
        tail = output.splitlines()[-20:]
        location = f"; log: {log_path}" if log_path else ""
        detail = "\n".join(tail)
        raise DeployExecutionError(
            f"command failed ({result.returncode}): {command.display}{location}"
            + (f"\n{detail}" if detail else "")
        )
    return result


def find_python(
    *,
    requested: str | None = None,
    workspace_root: Path | None = None,
    environ: Mapping[str, str] | None = None,
) -> str:
    """Select and validate a Python 3.11+ interpreter."""

    env = os.environ if environ is None else environ
    requested = (requested or env.get("REASBOOK_PYTHON_BIN") or env.get("REASBOOK_PYTHON") or "").strip()
    workspace = workspace_root or Path.cwd().parent
    candidates: list[str] = [requested] if requested else [
        str(workspace / "ReasBook" / "apps" / "reasbook-reviewer" / ".python311" / "bin" / "python"),
        str(workspace / "ReasBook" / "apps" / "reasbook-reviewer" / ".venv" / "bin" / "python"),
        str(workspace / ".python311" / "bin" / "python"),
        "python3.13",
        "python3.12",
        "python3.11",
        "python3",
        "python",
    ]
    for item in candidates:
        if not item:
            continue
        candidate = shutil.which(item) or (item if Path(item).is_file() else "")
        if not candidate:
            continue
        try:
            result = subprocess.run(
                [candidate, "-c", "import sys; print(*sys.version_info[:3])"],
                capture_output=True,
                text=True,
                check=False,
            )
            major, minor, *_ = (int(part) for part in result.stdout.split())
        except (OSError, ValueError):
            continue
        if result.returncode == 0 and (major, minor) >= (3, 11):
            return candidate
    raise DeployExecutionError("Python 3.11 or newer is required; set REASBOOK_PYTHON")


def find_elan(*, environ: Mapping[str, str] | None = None) -> Path | None:
    """Find an executable Elan installation without installing anything."""

    env = os.environ if environ is None else environ
    requested = env.get("REASBOOK_ELAN_BIN", "").strip()
    candidates = [Path(requested)] if requested else []
    home = Path(env.get("HOME", "/root"))
    candidates.append(Path(env.get("ELAN_HOME", str(home / ".elan"))) / "bin" / "elan")
    found = shutil.which("elan")
    if found:
        candidates.append(Path(found))
    for candidate in candidates:
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return candidate.resolve()
    return None


def ensure_toolchain(
    project_dir: Path,
    *,
    runner: Runner | None = None,
    dry_run: bool = False,
    environ: Mapping[str, str] | None = None,
) -> Path:
    """Ensure the project's toolchain is available and return its Lake path."""

    toolchain_file = project_dir / "lean-toolchain"
    if not toolchain_file.is_file():
        raise DeployExecutionError(f"missing {toolchain_file}")
    toolchain = toolchain_file.read_text(encoding="utf-8").strip()
    if not toolchain:
        raise DeployExecutionError(f"empty toolchain file: {toolchain_file}")
    elan = find_elan(environ=environ)
    if elan is None:
        lake = shutil.which("lake")
        if lake:
            return Path(lake).resolve()
        if dry_run:
            return Path("lake")
        raise DeployExecutionError("elan/lake not found; install elan or set REASBOOK_ELAN_BIN")
    listed = run_command(
        [str(elan), "toolchain", "list"],
        runner=runner,
        check=False,
        dry_run=dry_run,
    )
    installed = {line.split()[0] for line in listed.stdout.splitlines() if line.strip()}
    if toolchain not in installed:
        run_command(
            [str(elan), "toolchain", "install", toolchain],
            runner=runner,
            dry_run=dry_run,
        )
    lake = elan.parent / "lake"
    if not lake.is_file() and not dry_run:
        raise DeployExecutionError(f"elan is present but Lake is missing: {lake}")
    return lake.resolve() if lake.is_file() else Path(lake)


def prepare_external_lake(project_dir: Path, cache_dir: Path) -> None:
    """Move an in-checkout Lake tree aside and link the external cache."""

    project_dir = project_dir.expanduser().resolve()
    cache_dir = cache_dir.expanduser()
    if cache_dir.is_symlink():
        raise DeployExecutionError(f"cache directory must not be a symlink: {cache_dir}")
    resolved_cache = cache_dir.resolve(strict=False)
    if resolved_cache == project_dir or project_dir in resolved_cache.parents:
        raise DeployExecutionError(
            f"cache directory must be outside the project checkout: {cache_dir}"
        )
    cache_dir.mkdir(parents=True, exist_ok=True)
    lake_dir = project_dir / ".lake"
    if lake_dir.is_symlink():
        if lake_dir.resolve() == cache_dir.resolve():
            return
        lake_dir.unlink()
    elif lake_dir.exists():
        backup = cache_dir / f"legacy-lake-{time.time_ns()}-{os.getpid()}"
        shutil.move(str(lake_dir), str(backup))
    lake_dir.symlink_to(cache_dir, target_is_directory=True)


def prepare_cache_dirs(cache_root: Path) -> None:
    """Create the isolated cache layout used by all deployment stages."""

    for name in (
        "sources",
        "lake",
        "docs",
        "sites",
        "mathlib",
        "xdg",
        "logs",
        "locks",
        "manifests",
    ):
        (cache_root / name).mkdir(parents=True, exist_ok=True)


def lake_environment(cache_root: Path, key: str, *, create: bool = True) -> dict[str, str]:
    """Return branch/toolchain-isolated Mathlib and XDG cache variables."""

    environment = {
        "MATHLIB_CACHE_DIR": str(cache_root / "mathlib" / safe_name(key)),
        "XDG_CACHE_HOME": str(cache_root / "xdg"),
    }
    if create:
        Path(environment["MATHLIB_CACHE_DIR"]).mkdir(parents=True, exist_ok=True)
        Path(environment["XDG_CACHE_HOME"]).mkdir(parents=True, exist_ok=True)
    return environment


def prepare_project_runtime(
    project_dir: Path,
    *,
    cache_root: Path | None = None,
    cache_prefix: str = "",
    link_external_lake: bool = True,
    force_external_lake: bool = False,
    runner: Runner | None = None,
    dry_run: bool = False,
    environ: Mapping[str, str] | None = None,
) -> dict[str, str]:
    """Prepare one Lake project and return its child-process environment.

    This is the single runtime boundary used by repository build adapters. It
    selects Python and Lake, installs the pinned toolchain when needed, and
    keeps all generated state below the configured external cache.
    """

    env = {**os.environ, **dict(environ or {})}
    project = resolve_path(project_dir)
    if not project.is_dir():
        raise DeployExecutionError(f"Lake project does not exist: {project}")
    toolchain_file = project / "lean-toolchain"
    if not toolchain_file.is_file():
        raise DeployExecutionError(f"missing {toolchain_file}")
    toolchain = toolchain_file.read_text(encoding="utf-8").strip()
    if not toolchain:
        raise DeployExecutionError(f"empty toolchain file: {toolchain_file}")

    root = resolve_path(cache_root or default_cache_root(environ=env))
    if root == project or project in root.parents:
        raise DeployExecutionError(
            f"runtime cache must be outside the project checkout: {root}"
        )
    if not dry_run:
        prepare_cache_dirs(root)

    key = safe_name(toolchain.rsplit(":", 1)[-1])
    prefix = safe_name(cache_prefix) if cache_prefix else ""
    external_lake = root / "lake" / f"{prefix}{key}"
    lake_link = project / ".lake"
    preserve_link = lake_link.is_symlink() and not force_external_lake
    if link_external_lake and not dry_run:
        if preserve_link:
            existing_target = lake_link.resolve(strict=False)
            if existing_target == project or project in existing_target.parents:
                raise DeployExecutionError(
                    f"external Lake link resolves inside the project: {lake_link}"
                )
            print(
                f"[runtime] preserving external cache: {lake_link} -> "
                f"{os.readlink(lake_link)}"
            )
        else:
            prepare_external_lake(project, external_lake)

    lake = ensure_toolchain(project, runner=runner, dry_run=dry_run, environ=env)
    configured_lake = env.get("LAKE_BIN", "").strip()
    if configured_lake:
        selected_lake = shutil.which(configured_lake)
        if selected_lake is None and Path(configured_lake).is_file():
            selected_lake = str(Path(configured_lake).expanduser().resolve())
        if selected_lake is None:
            raise DeployExecutionError(
                f"configured Lake executable does not exist: {configured_lake}"
            )
        lake = Path(selected_lake)
    python = find_python(
        requested=(
            env.get("REASBOOK_PYTHON_BIN")
            or env.get("REASBOOK_PYTHON")
            or sys.executable
        ),
        workspace_root=project.parent.parent,
        environ=env,
    )
    runtime_env = lake_environment(root, key, create=not dry_run)
    for name in ("MATHLIB_CACHE_DIR", "XDG_CACHE_HOME"):
        configured = env.get(name, "").strip()
        if configured:
            path = resolve_path(configured)
            if not dry_run:
                path.mkdir(parents=True, exist_ok=True)
            runtime_env[name] = str(path)
    runtime_env.update(
        {
            "LAKE_BIN": str(lake),
            "REASBOOK_BUILD_LAKE_BIN": str(lake),
            "REASBOOK_CACHE_ROOT": str(root),
            "REASBOOK_PYTHON_BIN": python,
            "VERSO_LAKE_BIN": str(lake),
        }
    )
    elan = find_elan(environ=env)
    if elan is not None:
        runtime_env["REASBOOK_ELAN_BIN"] = str(elan)
        runtime_env["VERSO_ELAN_BIN"] = str(elan)
    return runtime_env


@contextmanager
def deployment_lock(cache_root: Path, *, enabled: bool = True) -> Iterator[None]:
    """Serialize writers sharing one deployment cache."""

    if not enabled:
        yield
        return
    lock_path = cache_root / "locks" / "deploy.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    handle = lock_path.open("a+", encoding="utf-8")
    try:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        yield
    finally:
        fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
        handle.close()


def write_json(path: Path, payload: object) -> None:
    """Publish deployment metadata atomically through the common helper."""

    try:
        atomic_write_json(path, payload)
    except (OSError, TypeError, ValueError) as exc:
        raise DeployExecutionError(f"could not write {path}: {exc}") from exc


__all__ = [
    "DEFAULT_CACHE_ROOT",
    "Runner",
    "default_cache_root",
    "deployment_lock",
    "ensure_toolchain",
    "find_elan",
    "find_python",
    "lake_environment",
    "prepare_cache_dirs",
    "prepare_external_lake",
    "prepare_project_runtime",
    "read_env_defaults",
    "resolve_path",
    "run_command",
    "safe_name",
    "timeout_from_env",
    "write_json",
]
