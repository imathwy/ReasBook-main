"""Atomic on-disk state for resumable release operations."""

from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime, timezone
import fcntl
import json
from pathlib import Path
from typing import Any, Iterator, Mapping

from reasbook_sdk_common import atomic_write_json

from ..errors import DeployConfigError, DeployExecutionError
from .models import RELEASE_ID_RE, ReleaseSpec
from .github import GitHubPublication
from .results import BundleInfo, ReleaseBuildReport, ReleaseManifest


STATE_STATUSES = {
    "planned",
    "building",
    "built",
    "validated",
    "packaged",
    "uploading",
    "dispatched",
    "published",
    "failed",
}


@dataclass(frozen=True)
class ReleaseLayout:
    cache_root: Path
    release_id: str

    def __post_init__(self) -> None:
        root = Path(self.cache_root).expanduser().resolve(strict=False)
        if not RELEASE_ID_RE.fullmatch(self.release_id):
            raise DeployConfigError(f"invalid release ID: {self.release_id!r}")
        object.__setattr__(self, "cache_root", root)

    @property
    def root(self) -> Path:
        return self.cache_root / "releases" / self.release_id

    @property
    def worktrees(self) -> Path:
        return self.root / "worktrees"

    @property
    def branch_sites(self) -> Path:
        return self.root / "branches"

    @property
    def logs(self) -> Path:
        return self.root / "logs"

    @property
    def site(self) -> Path:
        return self.root / "site"

    @property
    def spec(self) -> Path:
        return self.root / "release-spec.json"

    @property
    def profile(self) -> Path:
        return self.root / "profile.yml"

    @property
    def registry_snapshot(self) -> Path:
        return self.root / "toolchains.yml"

    @property
    def canonical_snapshot(self) -> Path:
        return self.root / "canonical-projects.yml"

    @property
    def state(self) -> Path:
        return self.root / "state.json"

    @property
    def build_report(self) -> Path:
        return self.root / "build-report.json"

    @property
    def manifest(self) -> Path:
        return self.root / "release-manifest.json"

    @property
    def bundle(self) -> Path:
        return self.root / f"{self.release_id}.site.tar.zst"

    @property
    def checksums(self) -> Path:
        return self.root / "SHA256SUMS"

    @property
    def bundle_info(self) -> Path:
        return self.root / "bundle.json"

    @property
    def publication(self) -> Path:
        return self.root / "publication.json"

    @property
    def lock(self) -> Path:
        return self.root / ".release.lock"


@dataclass(frozen=True)
class ReleaseState:
    release_id: str
    spec_digest: str
    status: str
    completed: tuple[str, ...]
    updated_at: str
    error: str | None = None

    def __post_init__(self) -> None:
        if self.status not in STATE_STATUSES:
            raise DeployConfigError(f"invalid release state: {self.status}")
        allowed = {"build", "site", "package", "publish"}
        if len(set(self.completed)) != len(self.completed) or any(
            stage not in allowed for stage in self.completed
        ):
            raise DeployConfigError("release state has invalid completed stages")

    def public_dict(self) -> dict[str, Any]:
        return {
            "schema_version": 1,
            "release_id": self.release_id,
            "spec_digest": self.spec_digest,
            "status": self.status,
            "completed": list(self.completed),
            "updated_at": self.updated_at,
            "error": self.error,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "ReleaseState":
        try:
            return cls(
                release_id=str(value["release_id"]),
                spec_digest=str(value["spec_digest"]),
                status=str(value["status"]),
                completed=tuple(str(item) for item in value["completed"]),
                updated_at=str(value["updated_at"]),
                error=str(value["error"]) if value.get("error") else None,
            )
        except (KeyError, TypeError, ValueError) as exc:
            raise DeployConfigError(f"invalid release state: {exc}") from exc


def _utc_now() -> str:
    return (
        datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z")
    )


class ReleaseStore:
    """Own release state persistence; callers own build and publish policy."""

    def __init__(self, layout: ReleaseLayout) -> None:
        self.layout = layout
        self._validate_root()

    def initialize(self, spec: ReleaseSpec) -> ReleaseState:
        self.layout.root.mkdir(parents=True, exist_ok=True)
        if self.layout.spec.is_file():
            existing = self.load_spec()
            if existing.spec_digest != spec.spec_digest:
                raise DeployExecutionError(
                    f"release ID collision at {self.layout.root}"
                )
        else:
            atomic_write_json(self.layout.spec, spec.public_dict())
        if self.layout.state.is_file():
            state = self.load_state()
            if state.spec_digest != spec.spec_digest:
                raise DeployExecutionError("release state/spec digest mismatch")
            return state
        state = ReleaseState(
            spec.release_id,
            spec.spec_digest,
            "planned",
            (),
            _utc_now(),
        )
        self.write_state(state)
        return state

    @staticmethod
    def find_by_digest(
        cache_root: Path,
        spec_digest: str,
    ) -> ReleaseSpec | None:
        releases = Path(cache_root).expanduser().resolve(strict=False) / "releases"
        if not releases.is_dir():
            return None
        candidates: list[ReleaseSpec] = []
        for path in releases.glob("site-*/release-spec.json"):
            try:
                value = json.loads(path.read_text(encoding="utf-8"))
                if isinstance(value, Mapping):
                    spec = ReleaseSpec.from_dict(value)
                    if spec.spec_digest == spec_digest:
                        candidates.append(spec)
            except (OSError, json.JSONDecodeError, DeployConfigError):
                continue
        return max(candidates, key=lambda item: item.resolved_at, default=None)

    def load_spec(self) -> ReleaseSpec:
        spec = ReleaseSpec.from_dict(self._read_json(self.layout.spec))
        if spec.release_id != self.layout.release_id:
            raise DeployExecutionError("ReleaseSpec belongs to another release")
        return spec

    def load_state(self) -> ReleaseState:
        state = ReleaseState.from_dict(self._read_json(self.layout.state))
        self._validate_identity(state.release_id, state.spec_digest)
        return state

    def load_build_report(self) -> ReleaseBuildReport:
        report = ReleaseBuildReport.from_dict(self._read_json(self.layout.build_report))
        self._validate_identity(report.release_id, report.spec_digest)
        return report

    def load_manifest(self) -> ReleaseManifest:
        manifest = ReleaseManifest.from_dict(self._read_json(self.layout.manifest))
        self._validate_identity(manifest.release_id, manifest.spec_digest)
        return manifest

    def load_bundle_info(self) -> BundleInfo:
        bundle = BundleInfo.from_dict(self._read_json(self.layout.bundle_info))
        if bundle.release_id != self.layout.release_id:
            raise DeployExecutionError("bundle belongs to another release")
        return bundle

    def load_publication(self) -> GitHubPublication:
        publication = GitHubPublication.from_dict(
            self._read_json(self.layout.publication)
        )
        if publication.release_id != self.layout.release_id:
            raise DeployExecutionError("publication belongs to another release")
        return publication

    def transition(
        self,
        status: str,
        *,
        completed_stage: str | None = None,
        error: str | None = None,
    ) -> ReleaseState:
        current = self.load_state()
        completed = list(current.completed)
        if completed_stage and completed_stage not in completed:
            completed.append(completed_stage)
        state = ReleaseState(
            current.release_id,
            current.spec_digest,
            status,
            tuple(completed),
            _utc_now(),
            error,
        )
        self.write_state(state)
        return state

    def write_state(self, state: ReleaseState) -> None:
        self._validate_identity(state.release_id, state.spec_digest)
        atomic_write_json(self.layout.state, state.public_dict())

    def write_build_report(self, report: ReleaseBuildReport) -> None:
        self._validate_identity(report.release_id, report.spec_digest)
        atomic_write_json(self.layout.build_report, report.public_dict())

    def write_manifest(self, manifest: ReleaseManifest) -> None:
        self._validate_identity(manifest.release_id, manifest.spec_digest)
        atomic_write_json(self.layout.manifest, manifest.public_dict())

    def write_bundle_info(self, bundle: BundleInfo) -> None:
        if bundle.release_id != self.layout.release_id:
            raise DeployExecutionError("bundle belongs to another release")
        atomic_write_json(self.layout.bundle_info, bundle.public_dict())

    def write_publication(self, publication: GitHubPublication) -> None:
        if publication.release_id != self.layout.release_id:
            raise DeployExecutionError("publication belongs to another release")
        atomic_write_json(self.layout.publication, publication.public_dict())

    @contextmanager
    def locked(self) -> Iterator[None]:
        self._validate_root()
        self.layout.root.mkdir(parents=True, exist_ok=True)
        with self.layout.lock.open("a+", encoding="utf-8") as handle:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)

    @staticmethod
    def _read_json(path: Path) -> dict[str, Any]:
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise DeployExecutionError(
                f"cannot read release file {path}: {exc}"
            ) from exc
        if not isinstance(value, Mapping):
            raise DeployExecutionError(f"release file must contain an object: {path}")
        return dict(value)

    def _validate_identity(self, release_id: str, spec_digest: str) -> None:
        if release_id != self.layout.release_id:
            raise DeployExecutionError("release file belongs to another release")
        spec = self.load_spec()
        if spec.spec_digest != spec_digest:
            raise DeployExecutionError("release file/spec digest mismatch")

    def _validate_root(self) -> None:
        root = self.layout.root
        if root.is_symlink() or root.parent.is_symlink():
            raise DeployExecutionError(f"release root must not be a symlink: {root}")
        resolved = root.resolve(strict=False)
        if self.layout.cache_root not in resolved.parents:
            raise DeployExecutionError(
                f"release root escapes the cache directory: {root}"
            )


__all__ = ["ReleaseLayout", "ReleaseState", "ReleaseStore"]
