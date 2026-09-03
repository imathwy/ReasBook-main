"""High-level Comparator preparation and execution."""

from __future__ import annotations

import fcntl
from contextlib import contextmanager
from typing import Iterator, Protocol

from reasbook_sdk_common import (
    Command,
    CommandExecutionError,
    CommandResult,
    CommandRunner,
    CommandTimeoutError,
    atomic_write_json,
)

from .commands import request_from_config
from .config import ComparatorConfig, validate_comparator_json
from .errors import ComparatorConfigError, ComparatorExecutionError
from .models import ComparisonResult, ComparatorRequest
from .project import verify_module_outputs


class RunnerLike(Protocol):
    def run(self, command: Command) -> CommandResult:
        """Execute one argv command."""


@contextmanager
def _project_locks(config: ComparatorConfig) -> Iterator[None]:
    """Serialize SDK writes to the target and Comparator `.lake` trees."""

    if not config.lock:
        yield
        return
    roots = sorted({config.project_root, config.comparator_root}, key=str)
    handles = []
    try:
        for root in roots:
            lock_path = root / ".lake" / ".comparator-sdk.lock"
            lock_path.parent.mkdir(parents=True, exist_ok=True)
            handle = lock_path.open("a+", encoding="utf-8")
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
            handles.append(handle)
        yield
    finally:
        for handle in reversed(handles):
            try:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
            finally:
                handle.close()


def _as_result(value: object, command: Command) -> CommandResult:
    """Normalize a compatible injected runner result."""

    if isinstance(value, CommandResult):
        return value
    try:
        return CommandResult(
            tuple(getattr(value, "argv", command.argv)),
            int(getattr(value, "returncode")),
            str(getattr(value, "stdout", "") or ""),
            str(getattr(value, "stderr", "") or ""),
            float(getattr(value, "duration_seconds", 0.0) or 0.0),
        )
    except (AttributeError, TypeError, ValueError) as exc:
        raise ComparatorConfigError(
            "injected command runner returned an invalid result"
        ) from exc


class ComparatorRunner:
    """Run one Comparator check with an injectable process executor."""

    def __init__(
        self,
        config: ComparatorConfig,
        *,
        runner: RunnerLike | None = None,
    ) -> None:
        self.config = config
        self.runner = runner or CommandRunner()
        self.request: ComparatorRequest | None = None

    def plan(self) -> ComparatorRequest:
        """Validate inputs and return commands without executing them."""

        self.config.validate()
        validate_comparator_json(self.config.config_path)
        self.request = request_from_config(self.config)
        return self.request

    def _run(self, command: Command) -> CommandResult:
        try:
            value = self.runner.run(command)
        except CommandTimeoutError:
            raise
        except CommandExecutionError:
            raise
        except Exception as exc:
            raise CommandExecutionError(
                f"command runner failed for {command.argv[0]!r}: {exc}"
            ) from exc
        return _as_result(value, command)

    def _failure(
        self,
        *,
        stage: str,
        error: str,
        command: tuple[str, ...] = (),
        preparation: tuple[CommandResult, ...] = (),
        returncode: int | None = None,
        timed_out: bool = False,
    ) -> ComparisonResult:
        result = ComparisonResult(
            status="timed_out" if timed_out else "error",
            returncode=returncode,
            stage=stage,
            error=error,
            command=command,
            preparation=preparation,
        )
        self._write_result(result)
        return result

    def _write_result(self, result: ComparisonResult) -> None:
        if self.config.result_file is not None:
            try:
                atomic_write_json(self.config.result_file, result.public_dict())
            except (OSError, TypeError, ValueError) as exc:
                raise ComparatorExecutionError(
                    f"could not write Comparator result: {self.config.result_file}"
                ) from exc

    def _prepare(
        self, request: ComparatorRequest
    ) -> tuple[CommandResult, ...] | ComparisonResult:
        results: list[CommandResult] = []
        for command in request.cache_commands:
            try:
                result = self._run(command)
            except CommandTimeoutError as exc:
                return self._failure(
                    stage="cache",
                    error=str(exc),
                    command=tuple(command.argv),
                    preparation=tuple(results),
                    timed_out=True,
                )
            except CommandExecutionError as exc:
                return self._failure(
                    stage="cache",
                    error=str(exc),
                    command=tuple(command.argv),
                    preparation=tuple(results),
                )
            results.append(result)
            if result.returncode != 0:
                return self._failure(
                    stage="cache",
                    error=f"cache preflight exited with status {result.returncode}",
                    command=tuple(command.argv),
                    preparation=tuple(results),
                    returncode=result.returncode,
                )

        if request.build_command is not None:
            command = request.build_command
            try:
                result = self._run(command)
            except CommandTimeoutError as exc:
                return self._failure(
                    stage="build",
                    error=str(exc),
                    command=tuple(command.argv),
                    preparation=tuple(results),
                    timed_out=True,
                )
            except CommandExecutionError as exc:
                return self._failure(
                    stage="build",
                    error=str(exc),
                    command=tuple(command.argv),
                    preparation=tuple(results),
                )
            results.append(result)
            if result.returncode != 0:
                return self._failure(
                    stage="build",
                    error=f"Comparator build exited with status {result.returncode}",
                    command=tuple(command.argv),
                    preparation=tuple(results),
                    returncode=result.returncode,
                )

        if not self.config.effective_comparator_bin.is_file():
            return self._failure(
                stage="build",
                error=f"Comparator executable does not exist: {self.config.effective_comparator_bin}",
                preparation=tuple(results),
            )
        return tuple(results)

    def compare(self, *, dry_run: bool = False) -> ComparisonResult:
        """Prepare and run Comparator, returning a structured verdict."""

        try:
            request = self.plan()
        except ComparatorConfigError as exc:
            return self._failure(stage="validate", error=str(exc))
        if dry_run:
            result = ComparisonResult(
                status="planned",
                stage="plan",
                command=tuple(request.compare_command.argv),
            )
            self._write_result(result)
            return result

        with _project_locks(self.config):
            prepared = self._prepare(request)
            if isinstance(prepared, ComparisonResult):
                return prepared
            try:
                command_result = self._run(request.compare_command)
            except CommandTimeoutError as exc:
                return self._failure(
                    stage="compare",
                    error=str(exc),
                    command=tuple(request.compare_command.argv),
                    preparation=prepared,
                    timed_out=True,
                )
            except CommandExecutionError as exc:
                return self._failure(
                    stage="compare",
                    error=str(exc),
                    command=tuple(request.compare_command.argv),
                    preparation=prepared,
                )

            if command_result.returncode == 0:
                status = "accepted"
                error: str | None = None
                if self.config.verify_outputs:
                    try:
                        data = validate_comparator_json(self.config.config_path)
                        modules = (
                            str(data["challenge_module"]),
                            str(data["solution_module"]),
                        )
                    except (ComparatorConfigError, KeyError, TypeError) as exc:
                        return self._failure(
                            stage="verify",
                            error=f"cannot inspect Comparator modules: {exc}",
                            command=tuple(command_result.argv),
                            preparation=prepared,
                            returncode=command_result.returncode,
                        )
                    missing = verify_module_outputs(self.config.project_root, modules)
                    if missing:
                        return self._failure(
                            stage="verify",
                            error="missing generated module outputs: "
                            + ", ".join(missing),
                            command=tuple(command_result.argv),
                            preparation=prepared,
                            returncode=command_result.returncode,
                        )
            elif command_result.returncode in {126, 127}:
                status = "error"
                error = (
                    f"Comparator could not start (status {command_result.returncode})"
                )
            else:
                status = "rejected"
                error = None

            result = ComparisonResult(
                status=status,
                returncode=command_result.returncode,
                stdout=command_result.stdout,
                stderr=command_result.stderr,
                duration_seconds=command_result.duration_seconds,
                stage="compare",
                error=error,
                command=tuple(command_result.argv),
                preparation=prepared,
            )
            self._write_result(result)
            return result

    run = compare


__all__ = ["ComparatorRunner", "RunnerLike"]
