"""Safe argv-based command execution shared by the capability SDKs."""

from __future__ import annotations

import math
import os
import re
import subprocess
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Mapping, Protocol, Sequence

from .errors import SdkError


def _terminate_process_group(process: subprocess.Popen[object]) -> None:
    """Stop a process and children spawned by tools such as Lake."""

    try:
        os.killpg(process.pid, 15)
    except (AttributeError, OSError):
        try:
            process.terminate()
        except OSError:
            return
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, 9)
        except (AttributeError, OSError):
            try:
                process.kill()
            except OSError:
                return
        process.wait()
    for stream in (process.stdin, process.stdout, process.stderr):
        if stream is not None:
            try:
                stream.close()
            except OSError:
                pass


_ENV_KEY = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


class CommandExecutionError(SdkError):
    """The requested process could not be started or completed."""

    def __init__(self, message: str, *, timed_out: bool = False) -> None:
        super().__init__(message)
        self.timed_out = timed_out


class CommandTimeoutError(CommandExecutionError):
    """The process exceeded its configured timeout."""

    def __init__(self, message: str) -> None:
        super().__init__(message, timed_out=True)


def _safe_argument(value: object, *, field: str) -> str:
    text = str(value)
    if not text or any(char in text for char in "\x00\r\n"):
        raise ValueError(f"{field} must be non-empty and contain no control characters")
    return text


def normalize_environment(
    values: Mapping[str, str] | Sequence[tuple[str, str]] | None,
) -> tuple[tuple[str, str], ...]:
    """Normalize and validate environment overrides in stable order."""

    if values is None:
        return ()
    items = values.items() if isinstance(values, Mapping) else values
    normalized: list[tuple[str, str]] = []
    for key, value in items:
        name = _safe_argument(key, field="environment variable name")
        if not _ENV_KEY.fullmatch(name):
            raise ValueError(f"invalid environment variable name: {name!r}")
        text = str(value)
        if any(char in text for char in "\x00\r\n"):
            raise ValueError(
                f"environment value for {name!r} contains a control character"
            )
        normalized.append((name, text))
    return tuple(normalized)


@dataclass(frozen=True)
class Command:
    """One executable invocation represented as an argument vector."""

    argv: Sequence[str]
    cwd: Path | str | None = None
    env: Mapping[str, str] | Sequence[tuple[str, str]] | None = None
    timeout: float | None = None
    input_text: str | None = None

    def __post_init__(self) -> None:
        normalized = tuple(
            _safe_argument(item, field="command argument") for item in self.argv
        )
        if not normalized:
            raise ValueError("command must contain at least one argument")
        object.__setattr__(self, "argv", normalized)
        if self.cwd is not None:
            path = Path(self.cwd).expanduser()
            if any(char in str(path) for char in "\x00\r\n"):
                raise ValueError(
                    "command working directory contains a control character"
                )
            if not path.is_absolute():
                path = path.resolve(strict=False)
            object.__setattr__(self, "cwd", path)
        object.__setattr__(self, "env", normalize_environment(self.env))
        if self.timeout is not None and (
            not math.isfinite(float(self.timeout)) or float(self.timeout) <= 0
        ):
            raise ValueError("command timeout must be a finite positive number")
        if self.input_text is not None and "\x00" in self.input_text:
            raise ValueError("command input cannot contain NUL")

    @property
    def env_dict(self) -> dict[str, str]:
        return dict(self.env or ())

    @property
    def display(self) -> str:
        import shlex

        return shlex.join(self.argv)

    @property
    def timeout_seconds(self) -> float | None:
        """Compatibility spelling for callers that use seconds explicitly."""

        return self.timeout


@dataclass(frozen=True)
class CommandResult:
    """Captured process output and timing information."""

    argv: tuple[str, ...] = ()
    returncode: int = 0
    stdout: str = ""
    stderr: str = ""
    duration_seconds: float = 0.0
    timed_out: bool = False
    command: Command | None = None

    def __post_init__(self) -> None:
        argv = tuple(self.argv)
        if self.command is not None and not argv:
            argv = self.command.argv
        object.__setattr__(self, "argv", argv)

    @property
    def succeeded(self) -> bool:
        return self.returncode == 0 and not self.timed_out

    @property
    def cwd(self) -> Path | None:
        return (
            self.command.cwd
            if self.command is not None and self.command.cwd is not None
            else None
        )


class CommandRunnerProtocol(Protocol):
    def run(self, command: Command) -> CommandResult:
        """Execute one command and return its result."""


@dataclass
class CommandRunner:
    """Default subprocess runner; callers may inject a compatible runner."""

    inherit_environment: bool = True
    stream: bool = False
    _clock: Callable[[], float] = field(default=time.monotonic, repr=False)
    output_file: Path | None = None
    _process: subprocess.Popen[str] | None = field(
        default=None, init=False, repr=False, compare=False
    )
    _process_lock: threading.Lock = field(
        default_factory=threading.Lock,
        init=False,
        repr=False,
        compare=False,
    )

    def terminate(self) -> None:
        """Terminate the active command and its process group, if any."""

        with self._process_lock:
            process = self._process
        if process is not None and process.poll() is None:
            _terminate_process_group(process)

    def run(self, command: Command) -> CommandResult:
        if command.cwd is not None and not command.cwd.is_dir():
            raise CommandExecutionError(
                f"working directory does not exist: {command.cwd}"
            )
        if command.env:
            environment = dict(command.env)
            if self.inherit_environment:
                environment = {**os.environ, **environment}
        elif self.inherit_environment:
            environment = dict(os.environ)
        else:
            environment = {}
        started = self._clock()
        output_handle = None
        process: subprocess.Popen[str] | None = None
        try:
            if self.output_file is not None:
                self.output_file.parent.mkdir(parents=True, exist_ok=True)
                output_handle = self.output_file.open("w", encoding="utf-8")
                stdout_target = output_handle
                stderr_target = subprocess.STDOUT
            else:
                stdout_target = None if self.stream else subprocess.PIPE
                stderr_target = None if self.stream else subprocess.PIPE
            process = subprocess.Popen(
                list(command.argv),
                cwd=str(command.cwd) if command.cwd is not None else None,
                env=environment,
                stdin=subprocess.PIPE if command.input_text is not None else None,
                text=True,
                stdout=stdout_target,
                stderr=stderr_target,
                start_new_session=True,
            )
            with self._process_lock:
                self._process = process
            stdout, stderr = process.communicate(
                input=command.input_text, timeout=command.timeout
            )
        except subprocess.TimeoutExpired as exc:
            _terminate_process_group(process)
            raise CommandTimeoutError(
                f"command timed out after {command.timeout:.1f}s: {command.display}"
            ) from exc
        except (OSError, ValueError) as exc:
            raise CommandExecutionError(f"cannot run {command.display}: {exc}") from exc
        except BaseException:
            self.terminate()
            raise
        finally:
            with self._process_lock:
                if self._process is process:
                    self._process = None
            if output_handle is not None:
                output_handle.close()
        if process is None:
            raise CommandExecutionError(f"cannot run {command.display}")
        stdout = stdout or ""
        stderr = stderr or ""
        return CommandResult(
            argv=command.argv,
            returncode=int(process.returncode),
            stdout=stdout,
            stderr=stderr,
            duration_seconds=max(0.0, self._clock() - started),
            command=command,
        )


def merged_environment(
    overrides: Mapping[str, str] | Sequence[tuple[str, str]] = (),
) -> dict[str, str]:
    """Return the process environment with validated overrides applied."""

    environment = dict(os.environ)
    environment.update(dict(normalize_environment(overrides)))
    return environment


__all__ = [
    "Command",
    "CommandExecutionError",
    "CommandResult",
    "CommandRunner",
    "CommandRunnerProtocol",
    "CommandTimeoutError",
    "merged_environment",
    "normalize_environment",
]
