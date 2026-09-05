"""Transport-neutral immutable fragments for distributed literate builds.

Each worker builds its assigned modules in a private Lake workspace, then
publishes only validated ``.json/.hash/.trace`` triples.  A barrier process
validates an exact, identity-bound partition before atomically installing a
normal literate cache that :class:`LiterateCacheBuilder` can reuse.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import tempfile
from dataclasses import dataclass
import fcntl
from contextlib import contextmanager
from typing import Any, Mapping, Sequence

from .literate import (
    LiterateArtifact,
    LiterateCacheBuilder,
    LiterateCacheError,
    LiterateCacheIdentity,
    _ordered_modules_digest,
)


_SCHEMA_VERSION = 1
_MANIFEST = "fragment.json"
_SHA256_RE = re.compile(r"sha256:[0-9a-f]{64}")
_PROJECT_KEY_RE = re.compile(r"(?:books|papers)/[A-Za-z0-9][A-Za-z0-9_.-]{0,160}")


def partition_modules(
    modules: Sequence[str], *, targets_per_job: int
) -> tuple[tuple[str, ...], ...]:
    """Return a deterministic exact partition suitable for a SiFlow manifest."""

    if isinstance(targets_per_job, bool) or not isinstance(targets_per_job, int):
        raise LiterateCacheError("targets_per_job must be an integer")
    if not 1 <= targets_per_job <= 256:
        raise LiterateCacheError("targets_per_job must be between 1 and 256")
    values = tuple(modules)
    if not values or len(values) != len(set(values)):
        raise LiterateCacheError("fragment module set must be non-empty and unique")
    return tuple(
        values[start : start + targets_per_job]
        for start in range(0, len(values), targets_per_job)
    )


@dataclass(frozen=True)
class LiterateFragmentIdentity:
    release_id: str
    spec_digest: str
    project_key: str
    parent: LiterateCacheIdentity
    batch_index: int
    batch_count: int
    modules: tuple[str, ...]

    def __post_init__(self) -> None:
        if not self.release_id or any(c in self.release_id for c in "\x00\r\n"):
            raise LiterateCacheError("release_id must be a non-empty safe string")
        if not _SHA256_RE.fullmatch(self.spec_digest):
            raise LiterateCacheError("spec_digest must be a full SHA-256")
        if not _PROJECT_KEY_RE.fullmatch(self.project_key):
            raise LiterateCacheError("project_key must be a canonical project key")
        if (
            isinstance(self.batch_index, bool)
            or isinstance(self.batch_count, bool)
            or not isinstance(self.batch_index, int)
            or not isinstance(self.batch_count, int)
            or self.batch_count < 1
            or not 0 <= self.batch_index < self.batch_count
        ):
            raise LiterateCacheError("invalid literate fragment batch coordinates")
        if not self.modules or len(self.modules) != len(set(self.modules)):
            raise LiterateCacheError("fragment modules must be non-empty and unique")

    @property
    def batch_sha256(self) -> str:
        payload = {
            "release_id": self.release_id,
            "spec_digest": self.spec_digest,
            "project_key": self.project_key,
            "parent": self.parent.public_dict(),
            "batch_index": self.batch_index,
            "batch_count": self.batch_count,
            "modules": list(self.modules),
        }
        encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
        return hashlib.sha256(encoded).hexdigest()

    def public_dict(self) -> dict[str, Any]:
        return {
            "release_id": self.release_id,
            "spec_digest": self.spec_digest,
            "project_key": self.project_key,
            "parent": self.parent.public_dict(),
            "batch_index": self.batch_index,
            "batch_count": self.batch_count,
            "modules": list(self.modules),
            "batch_sha256": self.batch_sha256,
        }


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.write_text(
        json.dumps(value, sort_keys=True, indent=2) + "\n", encoding="utf-8"
    )


def _artifact_files(root: Path, module: str) -> tuple[Path, Path, Path]:
    return LiterateCacheBuilder._artifact_paths_at(root, module)


def publish_fragment(
    source_literate_root: Path,
    fragment_root: Path,
    identity: LiterateFragmentIdentity,
) -> Path:
    """Validate and atomically publish one worker's immutable fragment."""

    requested_source = Path(source_literate_root)
    if requested_source.is_symlink():
        raise LiterateCacheError(
            f"fragment source must not be a symlink: {requested_source}"
        )
    source = requested_source.resolve(strict=True)
    requested_target = Path(fragment_root)
    if requested_target.is_symlink():
        raise LiterateCacheError(f"fragment target is unsafe: {requested_target}")
    if requested_target.exists():
        existing_identity, existing_artifacts = _read_fragment(requested_target)
        if (
            existing_identity != identity.public_dict()
            or tuple(item.module for item in existing_artifacts) != identity.modules
        ):
            raise LiterateCacheError(
                f"existing fragment identity mismatch: {requested_target}"
            )
        return requested_target / _MANIFEST
    if requested_target.parent.is_symlink():
        raise LiterateCacheError(
            f"fragment parent must not be a symlink: {requested_target.parent}"
        )
    target = requested_target.parent.resolve(strict=False) / requested_target.name
    target.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=f".{target.name}.", dir=target.parent))
    try:
        artifacts = tuple(
            LiterateCacheBuilder._validate_artifact_at(source, module)
            for module in identity.modules
        )
        for artifact in artifacts:
            source_files = _artifact_files(source, artifact.module)
            target_files = _artifact_files(stage, artifact.module)
            for source_file, target_file in zip(
                source_files, target_files, strict=True
            ):
                target_file.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source_file, target_file)
        _write_json(
            stage / _MANIFEST,
            {
                "schema_version": _SCHEMA_VERSION,
                "identity": identity.public_dict(),
                "artifacts": [item.public_dict() for item in artifacts],
            },
        )
        os.replace(stage, target)
        return target / _MANIFEST
    except BaseException:
        shutil.rmtree(stage, ignore_errors=True)
        raise


def _read_fragment(path: Path) -> tuple[dict[str, Any], tuple[LiterateArtifact, ...]]:
    requested = Path(path)
    if requested.is_symlink():
        raise LiterateCacheError(f"fragment root is unsafe: {path}")
    root = requested.resolve(strict=True)
    if not root.is_dir():
        raise LiterateCacheError(f"fragment root is unsafe: {path}")
    manifest = root / _MANIFEST
    try:
        value = json.loads(manifest.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise LiterateCacheError(f"invalid fragment manifest: {manifest}") from exc
    if not isinstance(value, dict) or value.get("schema_version") != _SCHEMA_VERSION:
        raise LiterateCacheError(f"invalid fragment manifest schema: {manifest}")
    identity = value.get("identity")
    records = value.get("artifacts")
    if not isinstance(identity, dict) or not isinstance(records, list):
        raise LiterateCacheError(f"incomplete fragment manifest: {manifest}")
    modules = identity.get("modules")
    if not isinstance(modules, list) or len(records) != len(modules):
        raise LiterateCacheError(f"incomplete fragment artifact set: {manifest}")
    artifacts = tuple(
        LiterateCacheBuilder._validate_artifact_at(root, str(module))
        for module in modules
    )
    if [item.public_dict() for item in artifacts] != records:
        raise LiterateCacheError(f"fragment artifact digest mismatch: {manifest}")
    expected = {_MANIFEST}
    for module in modules:
        expected.update(
            item.relative_to(root).as_posix()
            for item in _artifact_files(root, str(module))
        )
    found: set[str] = set()
    for item in root.rglob("*"):
        metadata = item.lstat()
        if stat.S_ISLNK(metadata.st_mode):
            raise LiterateCacheError(f"fragment contains a symlink: {item}")
        if stat.S_ISREG(metadata.st_mode):
            found.add(item.relative_to(root).as_posix())
        elif not stat.S_ISDIR(metadata.st_mode):
            raise LiterateCacheError(f"fragment contains a special file: {item}")
    if found != expected:
        raise LiterateCacheError(f"fragment file set is not exact: {manifest}")
    return identity, artifacts


@contextmanager
def _assembly_lock(destination: Path):
    lock = destination.parent / f".{destination.name}.assemble.lock"
    flags = os.O_CREAT | os.O_RDWR | getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(lock, flags, 0o644)
    except OSError as exc:
        raise LiterateCacheError(f"cannot open fragment assembly lock: {lock}") from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise LiterateCacheError(f"fragment assembly lock is not regular: {lock}")
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        yield
    finally:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        finally:
            os.close(descriptor)


def assemble_fragments(
    fragment_roots: Sequence[Path],
    destination_literate_root: Path,
    *,
    release_id: str,
    spec_digest: str,
    project_key: str,
    parent_identity: LiterateCacheIdentity,
    modules: Sequence[str],
) -> Path:
    """Validate the barrier and atomically install a complete literate cache."""

    expected_modules = tuple(modules)
    batches = partition_modules(expected_modules, targets_per_job=256)
    del batches  # validation above is intentionally shared with planning
    roots = tuple(Path(path) for path in fragment_roots)
    parsed = [_read_fragment(root) for root in roots]
    if not parsed:
        raise LiterateCacheError("fragment barrier contains no fragments")
    batch_count = len(parsed)
    by_index: dict[int, tuple[dict[str, Any], tuple[LiterateArtifact, ...], Path]] = {}
    for root, (identity, artifacts) in zip(roots, parsed, strict=True):
        expected_common = {
            "release_id": release_id,
            "spec_digest": spec_digest,
            "project_key": project_key,
            "parent": parent_identity.public_dict(),
            "batch_count": batch_count,
        }
        if any(identity.get(key) != value for key, value in expected_common.items()):
            raise LiterateCacheError(f"fragment identity mismatch: {root}")
        index = identity.get("batch_index")
        fragment_modules = identity.get("modules")
        if isinstance(index, bool) or not isinstance(index, int):
            raise LiterateCacheError(f"invalid fragment batch index: {root}")
        if index in by_index:
            raise LiterateCacheError(f"duplicate fragment batch index: {index}")
        if not isinstance(fragment_modules, list):
            raise LiterateCacheError(f"invalid fragment modules: {root}")
        reconstructed = LiterateFragmentIdentity(
            release_id,
            spec_digest,
            project_key,
            parent_identity,
            index,
            batch_count,
            tuple(str(item) for item in fragment_modules),
        )
        if identity.get("batch_sha256") != reconstructed.batch_sha256:
            raise LiterateCacheError(f"fragment batch digest mismatch: {root}")
        by_index[index] = identity, artifacts, root
    if set(by_index) != set(range(batch_count)):
        raise LiterateCacheError("fragment barrier has missing batch indices")
    ordered_modules = tuple(
        str(module)
        for index in range(batch_count)
        for module in by_index[index][0]["modules"]
    )
    if ordered_modules != expected_modules:
        raise LiterateCacheError("fragment barrier is not the exact ordered module set")
    if parent_identity.modules_sha256 != _ordered_modules_digest(expected_modules):
        raise LiterateCacheError("parent identity does not match full module set")

    destination = Path(destination_literate_root).resolve(strict=False)
    if destination.parent.is_symlink():
        raise LiterateCacheError(
            f"literate destination parent must not be a symlink: {destination.parent}"
        )
    destination.parent.mkdir(parents=True, exist_ok=True)
    marker = destination / ".reasbook-complete.json"
    if destination.is_dir() and not destination.is_symlink() and marker.is_file():
        try:
            existing = json.loads(marker.read_text(encoding="utf-8"))
            records = existing.get("artifacts") if isinstance(existing, dict) else None
            if (
                isinstance(existing, dict)
                and existing.get("schema_version") == 2
                and existing.get("identity") == parent_identity.public_dict()
                and isinstance(records, list)
                and len(records) == len(expected_modules)
            ):
                artifacts = tuple(
                    LiterateCacheBuilder._validate_artifact_at(destination, module)
                    for module in expected_modules
                )
                if [item.public_dict() for item in artifacts] == records:
                    return marker
        except (OSError, UnicodeError, json.JSONDecodeError, LiterateCacheError):
            pass
    stage = Path(tempfile.mkdtemp(prefix=".literate-assemble.", dir=destination.parent))
    backup = destination.parent / f".{destination.name}.previous"
    try:
        all_artifacts: list[LiterateArtifact] = []
        for index in range(batch_count):
            _identity, artifacts, root = by_index[index]
            for artifact in artifacts:
                all_artifacts.append(artifact)
                for source_file, target_file in zip(
                    _artifact_files(root, artifact.module),
                    _artifact_files(stage, artifact.module),
                    strict=True,
                ):
                    target_file.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(source_file, target_file)
        _write_json(
            stage / ".reasbook-complete.json",
            {
                "schema_version": 2,
                "identity": parent_identity.public_dict(),
                "artifacts": [item.public_dict() for item in all_artifacts],
            },
        )
        with _assembly_lock(destination):
            if backup.exists() or backup.is_symlink():
                raise LiterateCacheError(
                    f"stale literate assembly backup exists: {backup}"
                )
            had_destination = destination.exists() or destination.is_symlink()
            if had_destination:
                metadata = destination.lstat()
                if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISDIR(metadata.st_mode):
                    raise LiterateCacheError(
                        f"literate destination is unsafe: {destination}"
                    )
                os.replace(destination, backup)
            try:
                os.replace(stage, destination)
            except BaseException:
                if had_destination:
                    os.replace(backup, destination)
                raise
            if had_destination:
                shutil.rmtree(backup)
        return destination / ".reasbook-complete.json"
    except BaseException:
        shutil.rmtree(stage, ignore_errors=True)
        raise


__all__ = [
    "LiterateFragmentIdentity",
    "assemble_fragments",
    "partition_modules",
    "publish_fragment",
]
