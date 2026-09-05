"""Incremental, identity-bound caching for Verso literate module JSON."""

from __future__ import annotations

import argparse
import codecs
from concurrent.futures import ProcessPoolExecutor
from concurrent.futures.process import BrokenProcessPool
from contextlib import contextmanager
import fcntl
import hashlib
import json
import math
import mmap
from multiprocessing import get_context
import os
import platform
import re
import stat
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterator, Mapping, Sequence

from reasbook_sdk_common import Command, CommandExecutionError, CommandRunner

from .config import LEAN_ENV_NAMES
from .errors import VersoBuildError


_MODULE_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:[.][A-Za-z_][A-Za-z0-9_']*)*")
_HEX_16_RE = re.compile(r"[0-9a-f]{16}")
_HEX_40_RE = re.compile(r"[0-9a-f]{40}")
_HEX_64_RE = re.compile(r"[0-9a-f]{64}")
_SAFE_LABEL_RE = re.compile(r"[A-Za-z0-9_.:/@+-]+")
_MARKER_NAME = ".reasbook-complete.json"
_PROGRESS_NAME = ".reasbook-progress.json"
_LOCK_NAME = ".reasbook.lock"
_PROFILE = "reasbook-literate-v2"
_STATE_SCHEMA_VERSION = 2
_JSON_DOM_LIMIT = 8 * 1024 * 1024
_METADATA_LIMIT = 16 * 1024 * 1024
_JSON_WS_RE = re.compile(rb"[ \t\r\n]*")
_JSON_STRING_RE = re.compile(
    rb'"(?:[^"\\\x00-\x1f]|\\(?:["\\/bfnrt]|u[0-9A-Fa-f]{4}))*"'
)
_JSON_NUMBER_RE = re.compile(rb"-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?")
_MAX_JSON_DEPTH = 100_000
_IGNORED_CONCURRENCY_ENV = frozenset({"LAKE_JOBS"})


class LiterateCacheError(VersoBuildError):
    """The literate cache could not be validated or completed."""


class UnsafeLiterateCacheError(LiterateCacheError):
    """The cache contains a link or special file that must not be replaced."""


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _ordered_modules_digest(modules: Sequence[str]) -> str:
    encoded = json.dumps(
        list(modules), ensure_ascii=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _positive_int(value: object, *, field: str, maximum: int) -> int:
    if isinstance(value, bool):
        raise LiterateCacheError(f"{field} must be an integer")
    try:
        result = int(value)
    except (TypeError, ValueError) as exc:
        raise LiterateCacheError(f"{field} must be an integer") from exc
    if not 1 <= result <= maximum:
        raise LiterateCacheError(f"{field} must be between 1 and {maximum}")
    return result


def _positive_seconds(value: object, *, field: str) -> float:
    try:
        result = float(value)
    except (TypeError, ValueError) as exc:
        raise LiterateCacheError(f"{field} must be a positive number") from exc
    if not math.isfinite(result) or result <= 0:
        raise LiterateCacheError(f"{field} must be a positive number")
    return result


def load_module_manifest(path: Path) -> tuple[str, ...]:
    """Load the generator-owned module list without parsing generated Lean."""

    requested = Path(path).expanduser()
    if requested.is_symlink():
        raise UnsafeLiterateCacheError(
            f"module manifest must not be a symlink: {requested}"
        )
    manifest = requested.resolve(strict=True)
    if not manifest.is_file():
        raise LiterateCacheError(f"module manifest must be a regular file: {manifest}")
    try:
        payload = json.loads(manifest.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise LiterateCacheError(
            f"invalid literate module manifest: {manifest}"
        ) from exc
    if not isinstance(payload, dict) or payload.get("schema_version") != 1:
        raise LiterateCacheError("literate module manifest must use schema_version=1")
    raw_modules = payload.get("modules")
    if not isinstance(raw_modules, list) or not raw_modules:
        raise LiterateCacheError("literate module manifest contains no modules")
    modules: list[str] = []
    for index, raw in enumerate(raw_modules):
        if not isinstance(raw, str) or not _MODULE_RE.fullmatch(raw):
            raise LiterateCacheError(
                f"unsafe Lean module at manifest index {index}: {raw!r}"
            )
        modules.append(raw)
    if len(modules) != len(set(modules)):
        raise LiterateCacheError("literate module manifest contains duplicates")
    return tuple(modules)


@dataclass(frozen=True)
class LiterateCacheIdentity:
    branch: str
    commit: str
    lake_manifest_sha256: str
    toolchain: str
    architecture: str
    modules_sha256: str
    source_tree_sha256: str
    tooling_sha256: str
    profile: str = _PROFILE

    def __post_init__(self) -> None:
        if not self.branch or any(char in self.branch for char in "\x00\r\n"):
            raise LiterateCacheError("branch must be a non-empty safe string")
        if not _HEX_40_RE.fullmatch(self.commit):
            raise LiterateCacheError("commit must be a full lowercase Git SHA-1")
        if not _HEX_64_RE.fullmatch(self.lake_manifest_sha256):
            raise LiterateCacheError("lake_manifest_sha256 must be a full SHA-256")
        if not _HEX_64_RE.fullmatch(self.modules_sha256):
            raise LiterateCacheError("modules_sha256 must be a full SHA-256")
        if not _HEX_64_RE.fullmatch(self.source_tree_sha256):
            raise LiterateCacheError("source_tree_sha256 must be a full SHA-256")
        if not _HEX_64_RE.fullmatch(self.tooling_sha256):
            raise LiterateCacheError("tooling_sha256 must be a full SHA-256")
        for field, value in (
            ("toolchain", self.toolchain),
            ("architecture", self.architecture),
        ):
            if not value or not _SAFE_LABEL_RE.fullmatch(value):
                raise LiterateCacheError(f"{field} must be a non-empty safe string")

    def public_dict(self) -> dict[str, object]:
        return {
            "profile": self.profile,
            "branch": self.branch,
            "commit": self.commit,
            "lake_manifest_sha256": self.lake_manifest_sha256,
            "toolchain": self.toolchain,
            "architecture": self.architecture,
            "modules_sha256": self.modules_sha256,
            "source_tree_sha256": self.source_tree_sha256,
            "tooling_sha256": self.tooling_sha256,
        }


@dataclass(frozen=True)
class LiterateArtifact:
    module: str
    path: str
    size: int
    sha256: str
    lake_hash: str
    trace_sha256: str

    def public_dict(self) -> dict[str, object]:
        return {
            "module": self.module,
            "path": self.path,
            "size": self.size,
            "sha256": self.sha256,
            "lake_hash": self.lake_hash,
            "trace_sha256": self.trace_sha256,
        }


@dataclass(frozen=True)
class LiterateCacheResult:
    status: str
    reused: bool
    module_count: int
    scheduled_count: int
    batch_count: int
    marker: Path
    identity: LiterateCacheIdentity

    def public_dict(self) -> dict[str, object]:
        return {
            "status": self.status,
            "reused": self.reused,
            "module_count": self.module_count,
            "scheduled_count": self.scheduled_count,
            "batch_count": self.batch_count,
            "marker": str(self.marker),
            "identity": self.identity.public_dict(),
        }


class LiterateCacheBuilder:
    """Populate one exact branch cache while its caller owns the cache lock."""

    def __init__(
        self,
        *,
        lean_root: Path,
        module_manifest: Path,
        identity: LiterateCacheIdentity,
        lake_bin: str,
        jobs: int = 4,
        validation_jobs: int = 1,
        chunk_size: int = 32,
        batch_timeout_seconds: float = 3600.0,
        adopt_existing: bool = False,
        runner: Any | None = None,
        environ: Mapping[str, str] | None = None,
    ) -> None:
        self.lean_root = Path(lean_root).expanduser().resolve(strict=True)
        requested_manifest = Path(module_manifest).expanduser()
        if requested_manifest.is_symlink():
            raise UnsafeLiterateCacheError(
                f"module manifest must not be a symlink: {requested_manifest}"
            )
        self.module_manifest = requested_manifest.resolve(strict=True)
        self.identity = identity
        self.lake_bin = str(lake_bin)
        self.jobs = _positive_int(jobs, field="literate jobs", maximum=64)
        self.validation_jobs = _positive_int(
            validation_jobs, field="literate validation jobs", maximum=8
        )
        self.chunk_size = _positive_int(
            chunk_size, field="literate chunk size", maximum=256
        )
        self.batch_timeout_seconds = _positive_seconds(
            batch_timeout_seconds, field="literate batch timeout"
        )
        self.adopt_existing = bool(adopt_existing)
        self.environ = dict(environ if environ is not None else os.environ)
        self.runner = runner or CommandRunner(inherit_environment=False, stream=True)

        if not self.lean_root.is_dir():
            raise LiterateCacheError(f"Lean root is not a directory: {self.lean_root}")
        if not self.lake_bin or any(char in self.lake_bin for char in "\x00\r\n"):
            raise LiterateCacheError("lake_bin must be a non-empty safe argument")
        if not (
            (self.lean_root / "lakefile.lean").is_file()
            or (self.lean_root / "lakefile.toml").is_file()
        ):
            raise LiterateCacheError(f"Lean project not found: {self.lean_root}")
        lake_root = (self.lean_root / ".lake").resolve(strict=True)
        if not lake_root.is_dir():
            raise LiterateCacheError(
                f".lake does not resolve to a directory: {lake_root}"
            )
        self.literate_root = lake_root / "build" / "literate"
        self.marker = self.literate_root / _MARKER_NAME
        self.progress = self.literate_root / _PROGRESS_NAME
        self.lock = self.literate_root / _LOCK_NAME

    def run(self) -> LiterateCacheResult:
        self._prepare_literate_root()
        with self._cache_lock():
            return self._run_locked()

    def _run_locked(self) -> LiterateCacheResult:
        modules = load_module_manifest(self.module_manifest)
        expected_modules_digest = _ordered_modules_digest(modules)
        if self.identity.modules_sha256 != expected_modules_digest:
            raise LiterateCacheError(
                "module manifest digest does not match the requested cache identity"
            )
        self._assert_inputs_unchanged(modules)
        expected_identity = self.identity.public_dict()
        marker_was_present = self._state_exists(self.marker, label="completion marker")
        progress_was_present = self._state_exists(
            self.progress, label="progress marker"
        )
        marker = self._read_state(self.marker, label="completion marker")
        if marker is not None and marker.get("identity") == expected_identity:
            try:
                artifacts = self._validate_recorded_artifacts(
                    modules, marker.get("artifacts")
                )
            except UnsafeLiterateCacheError:
                raise
            except LiterateCacheError:
                artifacts = ()
            if artifacts:
                self._assert_inputs_unchanged(modules)
                return LiterateCacheResult(
                    "complete", True, len(modules), 0, 0, self.marker, self.identity
                )

        # A project finalizer often starts from a branch-finalizer cache whose
        # marker covers the complete branch module set.  Replaying Lake merely
        # because the requested ordered subset has another modules_sha256 is
        # unnecessary.  Adopt only records from a marker/progress state whose
        # complete source/toolchain/tooling identity is otherwise byte-for-byte
        # equal, then revalidate every requested JSON/hash/trace artifact.
        compatible: dict[str, LiterateArtifact] = {}
        if self.adopt_existing:
            compatible = self._validated_compatible_state(
                modules, marker, expected_identity
            )
            if len(compatible) != len(modules):
                progress_state = self._read_state(
                    self.progress, label="progress marker"
                )
                progress_compatible = self._validated_compatible_state(
                    modules, progress_state, expected_identity
                )
                compatible.update(progress_compatible)
            if len(compatible) == len(modules):
                self._assert_inputs_unchanged(modules)
                artifacts = tuple(compatible[module] for module in modules)
                payload = {
                    "schema_version": _STATE_SCHEMA_VERSION,
                    "identity": expected_identity,
                    "artifacts": [item.public_dict() for item in artifacts],
                }
                self._write_state(self.marker, payload)
                self._write_progress(modules, compatible, expected_identity)
                return LiterateCacheResult(
                    "complete", True, len(modules), 0, 0, self.marker, self.identity
                )

        self._remove_regular_state(self.marker, label="completion marker")
        valid = self._validated_progress(modules, expected_identity)
        valid.update(compatible)
        if (
            not valid
            and self.adopt_existing
            and not marker_was_present
            and not progress_was_present
        ):
            valid = self._adopt_existing_artifacts(modules)
            if valid:
                self._assert_inputs_unchanged(modules)
                self._write_progress(modules, valid, expected_identity)

        pending = [module for module in modules if module not in valid]
        for module in pending:
            self._remove_artifacts(module)

        batches = 0
        for start in range(0, len(pending), self.chunk_size):
            chunk = pending[start : start + self.chunk_size]
            self._run_batch(chunk)
            batch_artifacts = self._validate_generated_artifacts(chunk)
            if tuple(artifact.module for artifact in batch_artifacts) != tuple(chunk):
                raise LiterateCacheError(
                    "literate batch validation returned modules out of order"
                )
            valid.update({artifact.module: artifact for artifact in batch_artifacts})
            self._assert_inputs_unchanged(modules)
            batches += 1
            self._write_progress(modules, valid, expected_identity)

        self._assert_inputs_unchanged(modules)
        artifacts = tuple(valid[module] for module in modules)
        if len(artifacts) != len(modules):
            raise LiterateCacheError("literate cache is incomplete after all batches")
        payload = {
            "schema_version": _STATE_SCHEMA_VERSION,
            "identity": expected_identity,
            "artifacts": [item.public_dict() for item in artifacts],
        }
        self._write_state(self.marker, payload)
        return LiterateCacheResult(
            "complete",
            not pending,
            len(modules),
            len(pending),
            batches,
            self.marker,
            self.identity,
        )

    @contextmanager
    def _cache_lock(self) -> Iterator[None]:
        flags = os.O_CREAT | os.O_RDWR
        flags |= getattr(os, "O_CLOEXEC", 0)
        flags |= getattr(os, "O_NOFOLLOW", 0)
        try:
            descriptor = os.open(self.lock, flags, 0o644)
        except OSError as exc:
            raise UnsafeLiterateCacheError(
                f"cannot open literate cache lock safely: {self.lock}"
            ) from exc
        try:
            metadata = os.fstat(descriptor)
            if not stat.S_ISREG(metadata.st_mode):
                raise UnsafeLiterateCacheError(
                    f"literate cache lock must be a regular file: {self.lock}"
                )
            fcntl.flock(descriptor, fcntl.LOCK_EX)
            yield
        finally:
            try:
                fcntl.flock(descriptor, fcntl.LOCK_UN)
            finally:
                os.close(descriptor)

    def _prepare_literate_root(self) -> None:
        build = self.literate_root.parent
        if build.exists() and (build.is_symlink() or not build.is_dir()):
            raise UnsafeLiterateCacheError(f"Lake build path is unsafe: {build}")
        build.mkdir(parents=True, exist_ok=True)
        if self.literate_root.exists() and (
            self.literate_root.is_symlink() or not self.literate_root.is_dir()
        ):
            raise UnsafeLiterateCacheError(
                f"literate cache path is unsafe: {self.literate_root}"
            )
        self.literate_root.mkdir(parents=True, exist_ok=True)

    @staticmethod
    def _artifact_paths_at(literate_root: Path, module: str) -> tuple[Path, Path, Path]:
        relative = Path(*module.split(".")).with_suffix(".json")
        output = literate_root / relative
        cursor = literate_root
        for part in relative.parts[:-1]:
            cursor = cursor / part
            if cursor.is_symlink():
                raise UnsafeLiterateCacheError(
                    f"literate output parent must not be a symlink: {cursor}"
                )
            if cursor.exists() and not cursor.is_dir():
                raise UnsafeLiterateCacheError(
                    f"literate output parent is not a directory: {cursor}"
                )
        return output, Path(f"{output}.hash"), Path(f"{output}.trace")

    def _artifact_paths(self, module: str) -> tuple[Path, Path, Path]:
        return self._artifact_paths_at(self.literate_root, module)

    @staticmethod
    def _regular_file(path: Path, *, label: str) -> os.stat_result:
        try:
            metadata = path.lstat()
        except FileNotFoundError as exc:
            raise LiterateCacheError(f"missing {label}: {path}") from exc
        if stat.S_ISLNK(metadata.st_mode):
            raise UnsafeLiterateCacheError(f"{label} must not be a symlink: {path}")
        if not stat.S_ISREG(metadata.st_mode):
            raise LiterateCacheError(f"{label} must be a regular file: {path}")
        if metadata.st_size <= 0:
            raise LiterateCacheError(f"{label} must be non-empty: {path}")
        return metadata

    @staticmethod
    def _read_small(path: Path, *, label: str) -> bytes:
        metadata = LiterateCacheBuilder._regular_file(path, label=label)
        if metadata.st_size > _METADATA_LIMIT:
            raise LiterateCacheError(f"{label} is unexpectedly large: {path}")
        try:
            return path.read_bytes()
        except OSError as exc:
            raise LiterateCacheError(f"cannot read {label}: {path}") from exc

    @staticmethod
    def _validate_large_json_array(path: Path) -> None:
        """Validate complete JSON grammar from an mmap without building a DOM."""

        def fail(offset: int) -> None:
            raise LiterateCacheError(
                f"invalid literate JSON near byte {offset}: {path}"
            )

        try:
            with path.open("rb") as handle, mmap.mmap(
                handle.fileno(), 0, access=mmap.ACCESS_READ
            ) as content:
                length = len(content)

                def whitespace(position: int) -> int:
                    match = _JSON_WS_RE.match(content, position)
                    return match.end() if match is not None else position

                def string(position: int) -> int:
                    match = _JSON_STRING_RE.match(content, position)
                    if match is None:
                        fail(position)
                    return match.end()

                def value(position: int, stack: list[list[str]]) -> int:
                    position = whitespace(position)
                    if position >= length:
                        fail(position)
                    token = content[position]
                    if token == ord('"'):
                        return string(position)
                    if token == ord("["):
                        if len(stack) >= _MAX_JSON_DEPTH:
                            fail(position)
                        stack.append(["array", "value_or_end"])
                        return position + 1
                    if token == ord("{"):
                        if len(stack) >= _MAX_JSON_DEPTH:
                            fail(position)
                        stack.append(["object", "key_or_end"])
                        return position + 1
                    for literal in (b"true", b"false", b"null"):
                        if content[position : position + len(literal)] == literal:
                            return position + len(literal)
                    match = _JSON_NUMBER_RE.match(content, position)
                    if match is None:
                        fail(position)
                    return match.end()

                position = whitespace(0)
                if position >= length or content[position] != ord("["):
                    fail(position)
                position += 1
                stack: list[list[str]] = [["array", "value_or_end"]]
                while stack:
                    position = whitespace(position)
                    if position >= length:
                        fail(position)
                    kind, state = stack[-1]
                    token = content[position]
                    if kind == "array":
                        if state in {"value_or_end", "value"}:
                            if state == "value_or_end" and token == ord("]"):
                                stack.pop()
                                position += 1
                                continue
                            stack[-1][1] = "comma_or_end"
                            position = value(position, stack)
                            continue
                        if token == ord(","):
                            stack[-1][1] = "value"
                            position += 1
                            continue
                        if token == ord("]"):
                            stack.pop()
                            position += 1
                            continue
                        fail(position)

                    if state in {"key_or_end", "key"}:
                        if state == "key_or_end" and token == ord("}"):
                            stack.pop()
                            position += 1
                            continue
                        position = string(position)
                        stack[-1][1] = "colon"
                        continue
                    if state == "colon":
                        if token != ord(":"):
                            fail(position)
                        stack[-1][1] = "value"
                        position += 1
                        continue
                    if state == "value":
                        stack[-1][1] = "comma_or_end"
                        position = value(position, stack)
                        continue
                    if token == ord(","):
                        stack[-1][1] = "key"
                        position += 1
                        continue
                    if token == ord("}"):
                        stack.pop()
                        position += 1
                        continue
                    fail(position)

                if whitespace(position) != length:
                    fail(position)
        except LiterateCacheError:
            raise
        except (OSError, ValueError) as exc:
            raise LiterateCacheError(f"cannot validate literate JSON: {path}") from exc

    @staticmethod
    def _inspect_literate_json(path: Path, metadata: os.stat_result) -> str:
        """Hash and validate output without materializing huge JSON trees."""

        digest = hashlib.sha256()
        decoder = codecs.getincrementaldecoder("utf-8")()
        small = bytearray() if metadata.st_size <= _JSON_DOM_LIMIT else None
        try:
            with path.open("rb") as handle:
                for block in iter(lambda: handle.read(1024 * 1024), b""):
                    digest.update(block)
                    if small is not None:
                        small.extend(block)
                    decoder.decode(block)
                decoder.decode(b"", final=True)
        except (OSError, UnicodeDecodeError) as exc:
            raise LiterateCacheError(f"invalid UTF-8 literate JSON: {path}") from exc

        if small is not None:
            try:
                value = json.loads(small)
            except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                raise LiterateCacheError(f"invalid literate JSON: {path}") from exc
            if not isinstance(value, list):
                raise LiterateCacheError(f"literate JSON root must be an array: {path}")
        else:
            LiterateCacheBuilder._validate_large_json_array(path)
        return digest.hexdigest()

    @staticmethod
    def _validate_artifact_at(literate_root: Path, module: str) -> LiterateArtifact:
        output, hash_path, trace_path = LiterateCacheBuilder._artifact_paths_at(
            literate_root, module
        )
        metadata = LiterateCacheBuilder._regular_file(output, label="literate JSON")
        output_sha256 = LiterateCacheBuilder._inspect_literate_json(output, metadata)

        try:
            lake_hash = LiterateCacheBuilder._read_small(
                hash_path, label="Lake hash"
            ).decode("ascii")
        except (OSError, UnicodeDecodeError) as exc:
            raise LiterateCacheError(f"invalid Lake hash: {hash_path}") from exc
        if not _HEX_16_RE.fullmatch(lake_hash):
            raise LiterateCacheError(f"invalid Lake hash: {hash_path}")

        trace_bytes = LiterateCacheBuilder._read_small(trace_path, label="Lake trace")
        try:
            trace = json.loads(trace_bytes)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise LiterateCacheError(f"invalid Lake trace: {trace_path}") from exc
        if not isinstance(trace, dict):
            raise LiterateCacheError(f"Lake trace root must be an object: {trace_path}")

        relative = output.relative_to(literate_root).as_posix()
        return LiterateArtifact(
            module=module,
            path=relative,
            size=metadata.st_size,
            sha256=output_sha256,
            lake_hash=lake_hash,
            trace_sha256=hashlib.sha256(trace_bytes).hexdigest(),
        )

    def _validate_artifact(self, module: str) -> LiterateArtifact:
        return self._validate_artifact_at(self.literate_root, module)

    def _artifact_size_hint(self, module: str) -> int:
        """Return a non-authoritative scheduling hint without changing errors."""

        relative = Path(*module.split(".")).with_suffix(".json")
        cursor = self.literate_root
        for part in relative.parts[:-1]:
            cursor = cursor / part
            try:
                parent_metadata = cursor.lstat()
            except OSError:
                return 0
            if stat.S_ISLNK(parent_metadata.st_mode) or not stat.S_ISDIR(
                parent_metadata.st_mode
            ):
                return 0
        try:
            metadata = (self.literate_root / relative).lstat()
        except OSError:
            return 0
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
            return 0
        return max(0, metadata.st_size)

    def _validate_generated_artifacts(
        self, modules: Sequence[str]
    ) -> tuple[LiterateArtifact, ...]:
        """Validate one completed Lake batch without advancing its checkpoint."""

        if not modules:
            raise LiterateCacheError("literate validation batch must contain a module")
        size_hints = {module: self._artifact_size_hint(module) for module in modules}
        worker_count = min(self.validation_jobs, len(modules))
        print(
            "[verso-literate] "
            f"validate_targets={len(modules)} validation_workers={worker_count} "
            f"bytes={sum(size_hints.values())}",
            flush=True,
        )
        if worker_count == 1:
            return tuple(self._validate_artifact(module) for module in modules)

        # Submit large outputs first to reduce the tail from skewed generated
        # JSON sizes. Consume futures in manifest order so the first reported
        # artifact error remains deterministic and matches serial validation.
        indexed_modules = tuple(enumerate(modules))
        scheduled = sorted(
            indexed_modules,
            key=lambda item: (-size_hints[item[1]], item[0]),
        )
        executor = ProcessPoolExecutor(
            max_workers=worker_count,
            mp_context=get_context("spawn"),
        )
        futures = {}
        try:
            for _, module in scheduled:
                futures[module] = executor.submit(
                    _validate_artifact_process,
                    str(self.literate_root),
                    module,
                )
            return tuple(futures[module].result() for module in modules)
        except BrokenProcessPool as exc:
            raise LiterateCacheError(
                "literate artifact validation worker pool failed"
            ) from exc
        finally:
            executor.shutdown(wait=True, cancel_futures=True)

    def _artifact_from_record(self, module: str, raw: object) -> LiterateArtifact:
        output, _, _ = self._artifact_paths(module)
        expected_path = output.relative_to(self.literate_root).as_posix()
        if not isinstance(raw, dict):
            raise LiterateCacheError(f"invalid artifact record for {module}")
        if raw.get("module") != module or raw.get("path") != expected_path:
            raise LiterateCacheError(f"mismatched artifact record for {module}")
        size = raw.get("size")
        sha256 = raw.get("sha256")
        lake_hash = raw.get("lake_hash")
        trace_sha256 = raw.get("trace_sha256")
        if isinstance(size, bool) or not isinstance(size, int) or size <= 0:
            raise LiterateCacheError(f"invalid artifact size record for {module}")
        if not isinstance(sha256, str) or not _HEX_64_RE.fullmatch(sha256):
            raise LiterateCacheError(f"invalid artifact SHA-256 record for {module}")
        if not isinstance(lake_hash, str) or not _HEX_16_RE.fullmatch(lake_hash):
            raise LiterateCacheError(f"invalid Lake hash record for {module}")
        if not isinstance(trace_sha256, str) or not _HEX_64_RE.fullmatch(trace_sha256):
            raise LiterateCacheError(f"invalid trace SHA-256 record for {module}")
        return LiterateArtifact(
            module, expected_path, size, sha256, lake_hash, trace_sha256
        )

    def _validate_recorded_artifact(self, module: str, raw: object) -> LiterateArtifact:
        expected = self._artifact_from_record(module, raw)
        output, hash_path, trace_path = self._artifact_paths(module)
        metadata = self._regular_file(output, label="literate JSON")
        if metadata.st_size != expected.size or _sha256_file(output) != expected.sha256:
            raise LiterateCacheError(f"literate JSON no longer matches: {output}")
        try:
            lake_hash = self._read_small(hash_path, label="Lake hash").decode("ascii")
        except UnicodeDecodeError as exc:
            raise LiterateCacheError(f"invalid Lake hash: {hash_path}") from exc
        if lake_hash != expected.lake_hash:
            raise LiterateCacheError(f"Lake hash no longer matches: {hash_path}")
        trace_bytes = self._read_small(trace_path, label="Lake trace")
        if hashlib.sha256(trace_bytes).hexdigest() != expected.trace_sha256:
            raise LiterateCacheError(f"Lake trace no longer matches: {trace_path}")
        return expected

    def _validate_recorded_artifacts(
        self, modules: Sequence[str], raw_records: object
    ) -> tuple[LiterateArtifact, ...]:
        if not isinstance(raw_records, list) or len(raw_records) != len(modules):
            raise LiterateCacheError("completion marker artifact list is incomplete")
        return tuple(
            self._validate_recorded_artifact(module, raw)
            for module, raw in zip(modules, raw_records, strict=True)
        )

    def _remove_artifacts(self, module: str) -> None:
        for path in self._artifact_paths(module):
            try:
                metadata = path.lstat()
            except FileNotFoundError:
                continue
            if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
                raise UnsafeLiterateCacheError(
                    f"generated literate artifact is unsafe: {path}"
                )
            path.unlink()

    def _read_state(self, path: Path, *, label: str) -> dict[str, object] | None:
        try:
            metadata = path.lstat()
        except FileNotFoundError:
            return None
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
            raise UnsafeLiterateCacheError(f"{label} must be a regular file: {path}")
        if metadata.st_size <= 0 or metadata.st_size > _METADATA_LIMIT:
            return None
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError, json.JSONDecodeError):
            return None
        if (
            not isinstance(value, dict)
            or value.get("schema_version") != _STATE_SCHEMA_VERSION
        ):
            return None
        return value

    @staticmethod
    def _state_exists(path: Path, *, label: str) -> bool:
        try:
            metadata = path.lstat()
        except FileNotFoundError:
            return False
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
            raise UnsafeLiterateCacheError(f"{label} must be a regular file: {path}")
        return True

    def _assert_inputs_unchanged(self, modules: Sequence[str]) -> None:
        current_modules = load_module_manifest(self.module_manifest)
        if (
            tuple(modules) != current_modules
            or _ordered_modules_digest(current_modules) != self.identity.modules_sha256
        ):
            raise LiterateCacheError("literate module manifest changed during build")
        if _source_tree_digest(self.lean_root) != self.identity.source_tree_sha256:
            raise LiterateCacheError("Lean source tree changed during literate build")

    @staticmethod
    def _remove_regular_state(path: Path, *, label: str) -> None:
        try:
            metadata = path.lstat()
        except FileNotFoundError:
            return
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
            raise UnsafeLiterateCacheError(f"{label} must be a regular file: {path}")
        path.unlink()

    def _validated_progress(
        self, modules: Sequence[str], expected_identity: Mapping[str, object]
    ) -> dict[str, LiterateArtifact]:
        progress = self._read_state(self.progress, label="progress marker")
        if progress is None or progress.get("identity") != expected_identity:
            self._remove_regular_state(self.progress, label="progress marker")
            return {}
        records = progress.get("artifacts")
        if not isinstance(records, list):
            self._remove_regular_state(self.progress, label="progress marker")
            return {}
        allowed = set(modules)
        valid: dict[str, LiterateArtifact] = {}
        for raw in records:
            module = raw.get("module") if isinstance(raw, dict) else None
            if not isinstance(module, str) or module not in allowed or module in valid:
                self._remove_regular_state(self.progress, label="progress marker")
                return {}
            try:
                valid[module] = self._validate_recorded_artifact(module, raw)
            except UnsafeLiterateCacheError:
                raise
            except LiterateCacheError:
                self._remove_artifacts(module)
        self._write_progress(modules, valid, expected_identity)
        return valid

    def _validated_compatible_state(
        self,
        modules: Sequence[str],
        state: Mapping[str, object] | None,
        expected_identity: Mapping[str, object],
    ) -> dict[str, LiterateArtifact]:
        """Validate requested artifacts recorded by an exact-identity superset.

        ``modules_sha256`` is the sole permitted identity difference.  The
        current source tree and module manifest are independently rechecked by
        the caller before publication.
        """

        if state is None:
            return {}
        raw_identity = state.get("identity")
        if not isinstance(raw_identity, dict):
            return {}
        identity_without_modules = {
            key: value for key, value in raw_identity.items() if key != "modules_sha256"
        }
        expected_without_modules = {
            key: value
            for key, value in expected_identity.items()
            if key != "modules_sha256"
        }
        if (
            set(raw_identity) != set(expected_identity)
            or identity_without_modules != expected_without_modules
            or raw_identity.get("modules_sha256")
            == expected_identity.get("modules_sha256")
        ):
            return {}
        records = state.get("artifacts")
        if not isinstance(records, list):
            return {}
        requested = set(modules)
        selected: dict[str, object] = {}
        seen: set[str] = set()
        for raw in records:
            module = raw.get("module") if isinstance(raw, dict) else None
            if not isinstance(module, str) or module in seen:
                return {}
            seen.add(module)
            if module in requested:
                selected[module] = raw
        if set(selected) != requested:
            return {}
        valid: dict[str, LiterateArtifact] = {}
        for module in modules:
            try:
                valid[module] = self._validate_recorded_artifact(
                    module, selected[module]
                )
            except UnsafeLiterateCacheError:
                raise
            except LiterateCacheError:
                self._remove_artifacts(module)
        return valid

    def _adopt_existing_artifacts(
        self, modules: Sequence[str]
    ) -> dict[str, LiterateArtifact]:
        valid: dict[str, LiterateArtifact] = {}
        for module in modules:
            try:
                valid[module] = self._validate_artifact(module)
            except UnsafeLiterateCacheError:
                raise
            except LiterateCacheError:
                self._remove_artifacts(module)
        return valid

    def _write_progress(
        self,
        modules: Sequence[str],
        valid: Mapping[str, LiterateArtifact],
        expected_identity: Mapping[str, object],
    ) -> None:
        payload = {
            "schema_version": _STATE_SCHEMA_VERSION,
            "identity": dict(expected_identity),
            "artifacts": [
                valid[module].public_dict() for module in modules if module in valid
            ],
        }
        self._write_state(self.progress, payload)

    def _run_batch(self, modules: Sequence[str]) -> None:
        if not modules:
            raise LiterateCacheError("literate Lake batch must contain a module")
        environment = {
            key: value
            for key, value in self.environ.items()
            if key not in LEAN_ENV_NAMES and key not in _IGNORED_CONCURRENCY_ENV
        }
        # Lake is a generated Lean executable. Its runtime reads
        # ``LEAN_NUM_THREADS`` when initializing the task manager, so this is
        # the supported outer Job.async worker bound. Child compiler widths
        # remain owned by the caller's package configuration.
        environment["LEAN_NUM_THREADS"] = str(self.jobs)
        command = Command(
            (self.lake_bin, "build", *(f"+{module}:literate" for module in modules)),
            cwd=self.lean_root,
            env=environment,
            timeout=self.batch_timeout_seconds,
        )
        print(
            "[verso-literate] "
            f"targets={len(modules)} lake_workers={self.jobs} "
            "child_lean_threads=source-configured "
            f"first={modules[0]} last={modules[-1]}",
            flush=True,
        )
        try:
            result = self.runner.run(command)
        except CommandExecutionError as exc:
            raise LiterateCacheError(f"literate Lake batch failed: {exc}") from exc
        if result.returncode != 0:
            raise LiterateCacheError(
                f"literate Lake batch exited {result.returncode}: {command.display}"
            )

    def _write_state(self, path: Path, payload: Mapping[str, object]) -> None:
        encoded = (
            json.dumps(
                payload,
                ensure_ascii=True,
                indent=2,
                sort_keys=True,
            )
            + "\n"
        )
        descriptor, temporary_name = tempfile.mkstemp(
            dir=self.literate_root,
            prefix=f".{path.name}.",
            suffix=".tmp",
        )
        temporary = Path(temporary_name)
        try:
            with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
                handle.write(encoded)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, path)
        except BaseException:
            try:
                os.close(descriptor)
            except OSError:
                pass
            temporary.unlink(missing_ok=True)
            raise


def _validate_artifact_process(literate_root: str, module: str) -> LiterateArtifact:
    """Spawn-safe entry point for read-only generated artifact validation."""

    return LiterateCacheBuilder._validate_artifact_at(Path(literate_root), module)


def _git_value(root: Path, *args: str) -> str:
    try:
        return subprocess.check_output(
            ["git", "-C", str(root), *args],
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        raise LiterateCacheError(f"cannot derive Git identity for {root}") from exc


def _source_tree_digest(lean_root: Path) -> str:
    """Hash every local Lean/config input while excluding external build state."""

    selected: list[Path] = []
    for directory, names, files in os.walk(lean_root, followlinks=False):
        current = Path(directory)
        retained: list[str] = []
        for name in sorted(names):
            candidate = current / name
            if name in {".git", ".lake", "__pycache__", ".venv"}:
                continue
            if candidate.is_symlink():
                raise UnsafeLiterateCacheError(
                    f"source directory must not be a symlink: {candidate}"
                )
            retained.append(name)
        names[:] = retained
        for name in sorted(files):
            candidate = current / name
            if not (
                name.endswith(".lean")
                or name in {"lakefile.toml", "lean-toolchain", "lake-manifest.json"}
            ):
                continue
            if candidate.is_symlink() or not candidate.is_file():
                raise UnsafeLiterateCacheError(
                    f"source input must be a regular file: {candidate}"
                )
            selected.append(candidate)

    digest = hashlib.sha256()
    for path in sorted(
        selected, key=lambda item: item.relative_to(lean_root).as_posix()
    ):
        relative = path.relative_to(lean_root).as_posix().encode("utf-8")
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(bytes.fromhex(_sha256_file(path)))
    return digest.hexdigest()


def _bool_value(value: object, *, field: str) -> bool:
    if isinstance(value, bool):
        return value
    normalized = str(value).strip().lower()
    if normalized in {"1", "true", "yes", "on"}:
        return True
    if normalized in {"0", "false", "no", "off", ""}:
        return False
    raise LiterateCacheError(f"{field} must be true or false")


def _default_identity(
    lean_root: Path,
    modules: Sequence[str],
    environ: Mapping[str, str],
) -> LiterateCacheIdentity:
    actual_commit = _git_value(lean_root, "rev-parse", "HEAD")
    requested_commit = environ.get("REASBOOK_SOURCE_COMMIT")
    if requested_commit and requested_commit != actual_commit:
        raise LiterateCacheError(
            "REASBOOK_SOURCE_COMMIT does not match the checked-out Lean project"
        )
    branch = environ.get("REASBOOK_GITHUB_BRANCH")
    if not branch:
        try:
            branch = _git_value(lean_root, "symbolic-ref", "--short", "HEAD")
        except LiterateCacheError:
            branch = f"detached-{actual_commit[:12]}"
    commit = requested_commit or actual_commit
    manifest = lean_root / "lake-manifest.json"
    actual_manifest_digest = _sha256_file(manifest)
    manifest_digest = environ.get("REASBOOK_LAKE_MANIFEST_SHA256", "").removeprefix(
        "sha256:"
    )
    if manifest_digest and manifest_digest != actual_manifest_digest:
        raise LiterateCacheError(
            "REASBOOK_LAKE_MANIFEST_SHA256 does not match lake-manifest.json"
        )
    manifest_digest = manifest_digest or actual_manifest_digest
    actual_toolchain = (
        (lean_root / "lean-toolchain").read_text(encoding="utf-8").strip()
    )
    toolchain = environ.get("VERSO_TOOLCHAIN") or actual_toolchain
    if toolchain != actual_toolchain:
        raise LiterateCacheError(
            "VERSO_TOOLCHAIN does not match the checked-out Lean project"
        )
    architecture = environ.get("REASBOOK_CACHE_ARCHITECTURE") or platform.machine()
    tooling_digest = environ.get("REASBOOK_TOOLING_SHA256") or _sha256_file(
        Path(__file__)
    )
    return LiterateCacheIdentity(
        branch=branch,
        commit=commit,
        lake_manifest_sha256=manifest_digest.removeprefix("sha256:"),
        toolchain=toolchain,
        architecture=architecture,
        modules_sha256=_ordered_modules_digest(modules),
        source_tree_sha256=_source_tree_digest(lean_root),
        tooling_sha256=tooling_digest.removeprefix("sha256:"),
    )


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="verso-literate",
        description="Populate and verify an identity-bound Verso literate cache.",
    )
    parser.add_argument("--lean-root", type=Path, required=True)
    parser.add_argument("--module-manifest", type=Path, required=True)
    parser.add_argument("--lake-bin")
    parser.add_argument("--jobs", type=int)
    parser.add_argument(
        "--validation-jobs",
        type=int,
        help="spawned workers for read-only post-batch artifact validation (1-8)",
    )
    parser.add_argument("--chunk-size", type=int)
    parser.add_argument("--batch-timeout-seconds", type=float)
    parser.add_argument(
        "--adopt-existing",
        action="store_true",
        help="adopt valid unmarked artifacts from a caller-verified exact cache",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    environ = dict(os.environ)
    try:
        lean_root = args.lean_root.expanduser().resolve(strict=True)
        module_manifest = args.module_manifest.expanduser()
        modules = load_module_manifest(module_manifest)
        identity = _default_identity(lean_root, modules, environ)
        result = LiterateCacheBuilder(
            lean_root=lean_root,
            module_manifest=module_manifest,
            identity=identity,
            lake_bin=args.lake_bin or environ.get("REASBOOK_BUILD_LAKE_BIN") or "lake",
            jobs=args.jobs
            if args.jobs is not None
            else environ.get("REASBOOK_LITERATE_JOBS", "4"),
            validation_jobs=(
                args.validation_jobs
                if args.validation_jobs is not None
                else environ.get("REASBOOK_LITERATE_VALIDATION_JOBS", "1")
            ),
            chunk_size=args.chunk_size
            if args.chunk_size is not None
            else environ.get("REASBOOK_LITERATE_CHUNK_SIZE", "32"),
            batch_timeout_seconds=args.batch_timeout_seconds
            if args.batch_timeout_seconds is not None
            else environ.get("REASBOOK_LITERATE_BATCH_TIMEOUT_SECONDS", "3600"),
            adopt_existing=args.adopt_existing
            or _bool_value(
                environ.get("REASBOOK_LITERATE_ADOPT_EXISTING", "0"),
                field="REASBOOK_LITERATE_ADOPT_EXISTING",
            ),
            environ=environ,
        ).run()
        print(json.dumps(result.public_dict(), ensure_ascii=True, sort_keys=True))
        return 0
    except (LiterateCacheError, OSError, ValueError) as exc:
        print(f"verso-literate: {exc}", file=sys.stderr)
        return 2


__all__ = [
    "LiterateArtifact",
    "LiterateCacheBuilder",
    "LiterateCacheError",
    "LiterateCacheIdentity",
    "LiterateCacheResult",
    "UnsafeLiterateCacheError",
    "load_module_manifest",
    "main",
]


if __name__ == "__main__":
    raise SystemExit(main())
