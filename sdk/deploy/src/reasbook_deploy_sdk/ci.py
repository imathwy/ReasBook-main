"""CI/runtime helpers exposed as deploy-SDK subcommands.

These helpers are intentionally small adapters around the same path and
command policy used by :class:`DeploymentService`. Workflows call these
subcommands directly.
"""

from __future__ import annotations

from contextlib import contextmanager
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from typing import Mapping, Sequence

from .errors import DeployConfigError, DeployExecutionError
from .runtime import (
    DEFAULT_CACHE_ROOT,
    deployment_lock,
    find_elan,
    find_python,
    prepare_external_lake,
    resolve_path,
    Runner,
    run_command,
)


def _write_github_env(values: Mapping[str, str], *, environ: Mapping[str, str]) -> None:
    path = environ.get("GITHUB_ENV")
    if not path:
        return
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    for key, value in values.items():
        if any(char in str(value) for char in "\x00\r\n"):
            raise DeployConfigError(f"{key} contains a control character")
    with destination.open("a", encoding="utf-8") as handle:
        for key, value in values.items():
            handle.write(f"{key}={value}\n")


def _write_github_path(value: str, *, environ: Mapping[str, str]) -> None:
    path = environ.get("GITHUB_PATH")
    if not path:
        return
    destination = Path(path)
    if any(char in value for char in "\x00\r\n"):
        raise DeployConfigError("GITHUB_PATH value contains a control character")
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("a", encoding="utf-8") as handle:
        handle.write(f"{value}\n")


def _effective_env(environ: Mapping[str, str] | None) -> dict[str, str]:
    """Merge injected values with the process environment for child commands."""

    return {**os.environ, **dict(environ or {})}


def verify_python(*, environ: Mapping[str, str] | None = None) -> str:
    """Select Python 3.11+ and persist it for GitHub Actions when available."""

    env = _effective_env(environ)
    selected = find_python(environ=env, workspace_root=Path.cwd().parent)
    values = {"REASBOOK_PYTHON_BIN": selected}
    _write_github_env(values, environ=env)
    _write_github_path(str(Path(selected).parent), environ=env)
    print(f"[ci-python] using {selected}")
    return selected


def install_elan(
    *,
    environ: Mapping[str, str] | None = None,
    runner: Runner | None = None,
    dry_run: bool = False,
) -> Path:
    """Install Elan only when no executable installation is available."""

    env = _effective_env(environ)
    requested = env.get("ELAN_BIN") or env.get("REASBOOK_ELAN_BIN")
    if requested:
        candidate = Path(requested).expanduser()
        if not candidate.is_absolute():
            found = shutil.which(requested)
            candidate = Path(found) if found else candidate
        elan = candidate.resolve() if candidate.is_file() and os.access(candidate, os.X_OK) else None
    else:
        elan = find_elan(environ=env)
    if elan is None:
        explicit_home = env.get("ELAN_HOME", "").strip()
        if explicit_home:
            elan_home = Path(explicit_home).expanduser()
        elif requested:
            requested_path = Path(requested).expanduser()
            elan_home = (
                requested_path.parent.parent
                if requested_path.parent.name == "bin"
                else requested_path.parent
            )
        else:
            elan_home = Path(env.get("HOME", "/root")).expanduser() / ".elan"
        destination = (
            Path(requested).expanduser().resolve()
            if requested and not explicit_home
            else elan_home / "bin" / "elan"
        )
        if not dry_run:
            if shutil.which("curl") is None:
                raise DeployExecutionError("curl is required to install elan")
            download = run_command(
                ("curl", "-fsSL", "https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh"),
                runner=runner,
            )
            run_command(
                ("sh", "-s", "--", "-y"),
                runner=runner,
                env={"ELAN_HOME": str(elan_home)},
                input_text=download.stdout,
            )
        elan = destination
    if not elan.is_file() and not dry_run:
        raise DeployExecutionError(f"elan was not found after installation: {elan}")
    explicit_home = env.get("ELAN_HOME", "").strip()
    if explicit_home:
        elan_home = Path(explicit_home).expanduser()
    elif elan.parent.name == "bin":
        elan_home = elan.parent.parent
    else:
        # A custom binary can be used, but it does not imply an Elan home.
        elan_home = elan.parent
    elan_dir = elan.parent
    values = {
        "ELAN_HOME": str(elan_home),
        "ELAN_BIN": str(elan),
        "REASBOOK_ELAN_BIN": str(elan),
    }
    if elan.parent.name == "bin":
        values["LAKE_BIN"] = str(elan_home / "bin" / "lake")
    _write_github_env(values, environ=env)
    _write_github_path(str(elan_dir), environ=env)
    print(f"[ci-elan] using {elan}")
    return elan


def _valid_branch(branch: str) -> bool:
    if not branch or branch in {".", ".."}:
        return False
    if branch.startswith("/") or branch.endswith("/") or "//" in branch:
        return False
    if ".." in branch or "/./" in branch or branch.endswith("/."):
        return False
    return bool(re.fullmatch(r"[A-Za-z0-9._/-]+", branch))


def prepare_cache(
    branch: str,
    *,
    repo_root: str | Path | None = None,
    environ: Mapping[str, str] | None = None,
) -> Path:
    """Prepare a branch-isolated cache and link both Lake projects to it."""

    env = _effective_env(environ)
    if not _valid_branch(branch):
        raise DeployConfigError(f"invalid branch: {branch}")
    root = resolve_path(repo_root or env.get("REASBOOK_REPO_ROOT", Path.cwd()))
    lean_root = resolve_path(env.get("REASBOOK_LEAN_ROOT", root / "ReasBook"))
    web_root = resolve_path(env.get("REASBOOK_WEB_ROOT", root / "ReasBookWeb"))
    repo_key = re.sub(r"[^A-Za-z0-9._-]+", "_", env.get("GITHUB_REPOSITORY", "local")) or "local"
    configured_persist = env.get("PERSIST_ROOT", "").strip()
    configured_cache = env.get("REASBOOK_CACHE_ROOT", "").strip()
    default_cache = Path(configured_cache).expanduser() if configured_cache else DEFAULT_CACHE_ROOT
    default_persist = default_cache / "ci" / repo_key
    persist_base = resolve_path(configured_persist or default_persist)
    if persist_base == root or root in persist_base.parents:
        raise DeployConfigError(
            f"persistent cache must be outside the checkout: {persist_base}"
        )
    persist_root = persist_base / branch
    resolved_persist_root = persist_root.resolve(strict=False)
    if resolved_persist_root == root or root in resolved_persist_root.parents:
        raise DeployConfigError(
            f"persistent cache must be outside the checkout: {persist_root}"
        )
    if persist_root.is_symlink():
        raise DeployConfigError(f"persistent cache branch must not be a symlink: {persist_root}")
    values = {
        "PERSIST_ROOT": str(persist_root),
        "MATHLIB_CACHE_DIR": str(persist_root / "mathlib"),
        "XDG_CACHE_HOME": str(persist_root / "xdg"),
    }
    _write_github_env(values, environ=env)
    print(f"[ci-cache] using {persist_root}")
    with deployment_lock(persist_base, enabled=True):
        for child in ("reasbook_lake", "reasbookweb_lake", "mathlib", "xdg"):
            (persist_root / child).mkdir(parents=True, exist_ok=True)

        for project, target in (
            (lean_root, persist_root / "reasbook_lake"),
            (web_root, persist_root / "reasbookweb_lake"),
        ):
            if not project.is_dir():
                continue
            resolved_target = target.resolve(strict=False)
            if resolved_target == root or root in resolved_target.parents:
                raise DeployConfigError(
                    f"persistent cache target must be outside the checkout: {target}"
                )
            if target.is_symlink():
                raise DeployConfigError(f"persistent cache target must not be a symlink: {target}")
            prepare_external_lake(project, target)
        try:
            decompress_cache(persist_root / "reasbook_lake")
        except DeployExecutionError as exc:
            print(f"[ci-cache] warning: could not decompress persistent cache: {exc}", file=sys.stderr)
    return persist_root


def _terminate(process: subprocess.Popen[str]) -> None:
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except (AttributeError, OSError):
        process.terminate()
    try:
        process.wait(timeout=10)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except (AttributeError, OSError):
            process.kill()
        process.wait()


@contextmanager
def _forward_signals(process: subprocess.Popen[str]):
    """Forward CI cancellation signals to a supervised child process."""

    previous_term = signal.getsignal(signal.SIGTERM)
    previous_int = signal.getsignal(signal.SIGINT)

    def forward(signum: int, _frame: object) -> None:
        _terminate(process)
        raise SystemExit(128 + signum)

    signal.signal(signal.SIGTERM, forward)
    signal.signal(signal.SIGINT, forward)
    try:
        yield
    finally:
        signal.signal(signal.SIGTERM, previous_term)
        signal.signal(signal.SIGINT, previous_int)


def heartbeat(label: str, command: Sequence[str], *, environ: Mapping[str, str] | None = None) -> int:
    """Run a command while emitting periodic CI heartbeat lines."""

    env = _effective_env(environ)
    if not command:
        raise DeployConfigError("heartbeat requires a command")
    interval_raw = env.get("HEARTBEAT_INTERVAL_SECONDS", "60")
    try:
        interval = int(interval_raw)
    except ValueError:
        raise DeployConfigError("HEARTBEAT_INTERVAL_SECONDS must be a positive integer") from None
    if interval <= 0:
        raise DeployConfigError("HEARTBEAT_INTERVAL_SECONDS must be a positive integer")
    process = subprocess.Popen(list(command), env=env, start_new_session=True)
    started = time.monotonic()
    next_tick = started + interval
    print(f"::group::{label}")
    print(f"[ci][{label}] start {time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}")
    status: int | None = None
    try:
        with _forward_signals(process):
            while process.poll() is None:
                time.sleep(min(1.0, max(0.05, next_tick - time.monotonic())))
                if time.monotonic() >= next_tick and process.poll() is None:
                    print(f"[ci][{label}] heartbeat elapsed={int(time.monotonic() - started)}s")
                    next_tick += interval
            raw_status = process.wait()
            status = 128 + (-raw_status) if raw_status < 0 else raw_status
    except SystemExit as exc:
        try:
            status = int(exc.code)
        except (TypeError, ValueError):
            status = 1
        raise
    finally:
        elapsed = int(time.monotonic() - started)
        shown_status = status if status is not None else 143
        print(f"[ci][{label}] end elapsed={elapsed}s exit={shown_status}")
        print("::endgroup::")
    assert status is not None
    return status


def retry_on_143(command: Sequence[str], *, environ: Mapping[str, str] | None = None) -> int:
    """Retry a command when it exits with the conventional SIGTERM status."""

    env = _effective_env(environ)
    if not command:
        raise DeployConfigError("retry-143 requires a command")
    try:
        retries = int(env.get("RETRY_ON_143_MAX_RETRIES", "1"))
    except ValueError:
        raise DeployConfigError("RETRY_ON_143_MAX_RETRIES must be a non-negative integer") from None
    if retries < 0:
        raise DeployConfigError("RETRY_ON_143_MAX_RETRIES must be a non-negative integer")
    try:
        delay = float(env.get("RETRY_ON_143_SLEEP_SECONDS", "15"))
    except ValueError:
        raise DeployConfigError("RETRY_ON_143_SLEEP_SECONDS must be a non-negative number") from None
    if delay < 0:
        raise DeployConfigError("RETRY_ON_143_SLEEP_SECONDS must be a non-negative number")
    for attempt in range(1, retries + 2):
        print(f"[ci][retry143] attempt {attempt}/{retries + 1}")
        process = subprocess.Popen(list(command), env=env, start_new_session=True)
        try:
            with _forward_signals(process):
                raw_status = process.wait()
        except SystemExit:
            raise
        status = 128 + (-raw_status) if raw_status < 0 else raw_status
        if status != 143 or attempt > retries:
            return status
        time.sleep(delay)
    return 1


def compress_cache(
    lake_dir: str | Path,
    *,
    runner: Runner | None = None,
    timeout_seconds: float = 1800.0,
) -> None:
    """Compress heavy persistent-cache subtrees and remove their expanded form."""

    root = Path(lake_dir).expanduser().resolve()
    build = root / "build"
    if not root.is_dir():
        raise DeployConfigError(f"lake directory does not exist: {root}")
    if not build.is_dir():
        print(f"[compress-cache] no build directory at {build}; skipping")
        return
    for name in ("ir", "literate"):
        source = build / name
        archive = build / f"{name}.tar.zst"
        if not source.is_dir():
            continue
        if archive.is_symlink():
            raise DeployConfigError(f"refusing to overwrite symlink: {archive}")
        temporary = build / f".{name}.tar.zst.{os.getpid()}.{time.time_ns()}"
        try:
            run_command(
                ["tar", "--zstd", "-cf", str(temporary), "-C", str(build), name],
                runner=runner,
                timeout=timeout_seconds,
            )
            os.replace(temporary, archive)
        except (DeployExecutionError, OSError, subprocess.CalledProcessError) as exc:
            Path(temporary).unlink(missing_ok=True)
            raise DeployExecutionError(f"could not compress {source}: {exc}") from exc
        shutil.rmtree(source)
        print(f"[compress-cache] {name} -> {archive}")


def decompress_cache(
    lake_dir: str | Path,
    *,
    runner: Runner | None = None,
    timeout_seconds: float = 1800.0,
) -> None:
    """Expand persistent-cache archives when an uncompressed tree is absent."""

    root = Path(lake_dir).expanduser().resolve()
    build = root / "build"
    if not root.is_dir():
        raise DeployConfigError(f"lake directory does not exist: {root}")
    if not build.is_dir():
        return
    for name in ("ir", "literate"):
        target = build / name
        archive = build / f"{name}.tar.zst"
        if target.exists() or not archive.is_file():
            continue
        _validate_archive(archive, name, runner=runner, timeout_seconds=timeout_seconds)
        stage = Path(tempfile.mkdtemp(prefix=f".{name}-extract-", dir=build))
        try:
            run_command(
                ["tar", "--zstd", "-xf", str(archive), "-C", str(stage)],
                runner=runner,
                timeout=timeout_seconds,
            )
            extracted = stage / name
            if not extracted.is_dir() or extracted.is_symlink():
                raise DeployExecutionError(
                    f"archive did not contain a regular {name}/ directory"
                )
            os.replace(extracted, target)
        except (DeployExecutionError, OSError, subprocess.CalledProcessError) as exc:
            raise DeployExecutionError(f"could not decompress {archive}: {exc}") from exc
        finally:
            shutil.rmtree(stage, ignore_errors=True)
        print(f"[decompress-cache] {archive} -> {target}")


def _validate_archive(
    archive: Path,
    expected_root: str,
    *,
    runner: Runner | None = None,
    timeout_seconds: float = 1800.0,
) -> None:
    """Reject traversal and link members before extracting a shared cache."""

    try:
        listing = run_command(
            ["tar", "--zstd", "-tvf", str(archive)],
            runner=runner,
            timeout=timeout_seconds,
        ).stdout.splitlines()
    except DeployExecutionError as exc:
        raise DeployExecutionError(f"could not inspect archive {archive}: {exc}") from exc
    for line in listing:
        if not line.strip():
            continue
        mode = line.split(maxsplit=1)[0]
        if mode[:1] in {"l", "h"}:
            raise DeployConfigError(f"archive contains a link member: {archive}")
        fields = line.split(maxsplit=5)
        if len(fields) < 6:
            raise DeployConfigError(f"malformed archive member in {archive}") from None
        name = fields[5]
        parts = Path(name).parts
        if Path(name).is_absolute() or ".." in parts:
            raise DeployConfigError(f"unsafe archive member {name!r}")
        if name != expected_root and not name.startswith(expected_root + "/"):
            raise DeployConfigError(
                f"archive member escapes {expected_root}/: {name!r}"
            )


__all__ = [
    "compress_cache",
    "decompress_cache",
    "heartbeat",
    "install_elan",
    "prepare_cache",
    "retry_on_143",
    "verify_python",
]
