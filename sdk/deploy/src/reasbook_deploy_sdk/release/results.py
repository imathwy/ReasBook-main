"""Build evidence and portable release-manifest models."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any, Mapping

from ..errors import DeployConfigError
from .models import (
    ARTIFACT_NAME_RE,
    RELEASE_ID_RE,
    ReleaseSpec,
    SHA256_RE,
)


@dataclass(frozen=True)
class StageOutcome:
    name: str
    status: str
    message: str = ""
    log: str | None = None

    def __post_init__(self) -> None:
        if self.status not in {"success", "failed", "skipped"}:
            raise DeployConfigError(f"invalid stage status: {self.status!r}")

    @property
    def succeeded(self) -> bool:
        return self.status in {"success", "skipped"}

    def public_dict(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "status": self.status,
            "message": self.message,
            "log": self.log,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "StageOutcome":
        return cls(
            name=str(value["name"]),
            status=str(value["status"]),
            message=str(value.get("message") or ""),
            log=str(value["log"]) if value.get("log") else None,
        )


@dataclass(frozen=True)
class BranchBuildResult:
    branch: str
    commit: str
    status: str
    site_root: str | None
    stages: tuple[StageOutcome, ...]
    error: str | None = None

    def __post_init__(self) -> None:
        if self.status not in {"success", "degraded", "failed"}:
            raise DeployConfigError(f"invalid branch build status: {self.status}")

    @property
    def succeeded(self) -> bool:
        return self.status in {"success", "degraded"}

    def public_dict(self) -> dict[str, Any]:
        return {
            "branch": self.branch,
            "commit": self.commit,
            "status": self.status,
            "site_root": self.site_root,
            "stages": [stage.public_dict() for stage in self.stages],
            "error": self.error,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "BranchBuildResult":
        return cls(
            branch=str(value["branch"]),
            commit=str(value["commit"]),
            status=str(value["status"]),
            site_root=(str(value["site_root"]) if value.get("site_root") else None),
            stages=tuple(StageOutcome.from_dict(item) for item in value["stages"]),
            error=str(value["error"]) if value.get("error") else None,
        )


@dataclass(frozen=True)
class ReleaseBuildReport:
    release_id: str
    spec_digest: str
    status: str
    branches: tuple[BranchBuildResult, ...]

    def __post_init__(self) -> None:
        if self.status not in {"success", "degraded", "failed"}:
            raise DeployConfigError(f"invalid release build status: {self.status}")
        if not SHA256_RE.fullmatch(self.spec_digest):
            raise DeployConfigError("build report has an invalid spec digest")

    @classmethod
    def from_branches(
        cls,
        spec: ReleaseSpec,
        branches: tuple[BranchBuildResult, ...],
    ) -> "ReleaseBuildReport":
        if any(not result.succeeded for result in branches):
            status = "failed"
        elif any(result.status == "degraded" for result in branches):
            status = "degraded"
        else:
            status = "success"
        return cls(spec.release_id, spec.spec_digest, status, branches)

    def public_dict(self) -> dict[str, Any]:
        return {
            "schema_version": 1,
            "release_id": self.release_id,
            "spec_digest": self.spec_digest,
            "status": self.status,
            "branches": [branch.public_dict() for branch in self.branches],
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "ReleaseBuildReport":
        try:
            return cls(
                release_id=str(value["release_id"]),
                spec_digest=str(value["spec_digest"]),
                status=str(value["status"]),
                branches=tuple(
                    BranchBuildResult.from_dict(item) for item in value["branches"]
                ),
            )
        except (KeyError, TypeError, ValueError) as exc:
            raise DeployConfigError(f"invalid build report: {exc}") from exc


@dataclass(frozen=True)
class ReleaseManifest:
    release_id: str
    spec_digest: str
    status: str
    base_path: str
    generated_at: str
    site_tree_sha256: str
    file_count: int
    total_bytes: int
    projects: tuple[dict[str, Any], ...]
    branches: tuple[dict[str, Any], ...]
    artifact: str = "full"

    def __post_init__(self) -> None:
        release_match = RELEASE_ID_RE.fullmatch(self.release_id)
        if not release_match:
            raise DeployConfigError("release manifest has an invalid release ID")
        if self.status not in {"success", "degraded"}:
            raise DeployConfigError("only a successful build can be packaged")
        if not SHA256_RE.fullmatch(self.spec_digest):
            raise DeployConfigError("release manifest has an invalid spec digest")
        if (
            release_match.group("digest")
            != self.spec_digest.removeprefix("sha256:")[:12]
        ):
            raise DeployConfigError(
                "release manifest ID does not match its spec digest"
            )
        if not SHA256_RE.fullmatch(self.site_tree_sha256):
            raise DeployConfigError("release manifest has an invalid site digest")
        if (
            not self.base_path.startswith("/")
            or not self.base_path.endswith("/")
            or "//" in self.base_path
            or ".." in self.base_path
        ):
            raise DeployConfigError("release manifest has an invalid base path")
        try:
            datetime.fromisoformat(self.generated_at.replace("Z", "+00:00"))
        except ValueError as exc:
            raise DeployConfigError(
                "release manifest generated_at must be an ISO timestamp"
            ) from exc
        if self.file_count < 1 or self.total_bytes < 1:
            raise DeployConfigError("release site must contain files")
        if not ARTIFACT_NAME_RE.fullmatch(self.artifact):
            raise DeployConfigError("release manifest has an invalid artifact name")
        project_fields = {
            "key",
            "kind",
            "project_id",
            "slug",
            "branch",
            "commit",
            "source_path",
            "build_target",
            "canonical",
            "outputs",
            "status",
        }
        if any(set(project) != project_fields for project in self.projects):
            raise DeployConfigError("release manifest project fields are invalid")
        if any(
            project.get("status") not in {"success", "degraded"}
            for project in self.projects
        ):
            raise DeployConfigError("release manifest project status is invalid")
        branch_fields = {"branch", "commit", "status", "stages"}
        if any(set(branch) != branch_fields for branch in self.branches):
            raise DeployConfigError("release manifest branch fields are invalid")
        for branch in self.branches:
            if branch.get("status") not in {"success", "degraded"}:
                raise DeployConfigError("release manifest branch status is invalid")
            stages = branch.get("stages")
            if not isinstance(stages, list) or any(
                not isinstance(stage, Mapping)
                or set(stage) != {"name", "status"}
                or stage.get("status") not in {"success", "failed", "skipped"}
                for stage in stages
            ):
                raise DeployConfigError("release manifest stage fields are invalid")

    def public_dict(self) -> dict[str, Any]:
        return {
            "schema_version": 2,
            "release_id": self.release_id,
            "spec_digest": self.spec_digest,
            "artifact": self.artifact,
            "status": self.status,
            "base_path": self.base_path,
            "generated_at": self.generated_at,
            "site_tree_sha256": self.site_tree_sha256,
            "file_count": self.file_count,
            "total_bytes": self.total_bytes,
            "projects": list(self.projects),
            "branches": list(self.branches),
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "ReleaseManifest":
        try:
            common = {
                "schema_version",
                "release_id",
                "spec_digest",
                "status",
                "base_path",
                "generated_at",
                "site_tree_sha256",
                "file_count",
                "total_bytes",
                "projects",
                "branches",
            }
            version = value.get("schema_version")
            expected = common if version == 1 else common | {"artifact"}
            if version not in {1, 2} or set(value) != expected:
                raise DeployConfigError(
                    "release manifest fields do not match its schema version"
                )
            return cls(
                release_id=str(value["release_id"]),
                spec_digest=str(value["spec_digest"]),
                status=str(value["status"]),
                base_path=str(value["base_path"]),
                generated_at=str(value["generated_at"]),
                site_tree_sha256=str(value["site_tree_sha256"]),
                file_count=int(value["file_count"]),
                total_bytes=int(value["total_bytes"]),
                projects=tuple(dict(item) for item in value["projects"]),
                branches=tuple(dict(item) for item in value["branches"]),
                artifact=str(value.get("artifact", "full")),
            )
        except (KeyError, TypeError, ValueError) as exc:
            raise DeployConfigError(f"invalid release manifest: {exc}") from exc


@dataclass(frozen=True)
class BundleInfo:
    release_id: str
    bundle: str
    manifest: str
    checksums: str
    bundle_sha256: str
    artifact: str = "full"
    release_set: str | None = None

    def __post_init__(self) -> None:
        if not RELEASE_ID_RE.fullmatch(self.release_id):
            raise DeployConfigError("bundle has an invalid release ID")
        if not SHA256_RE.fullmatch(self.bundle_sha256):
            raise DeployConfigError("bundle checksum is invalid")
        if not ARTIFACT_NAME_RE.fullmatch(self.artifact):
            raise DeployConfigError("bundle has an invalid artifact name")

    def public_dict(self) -> dict[str, Any]:
        return {
            "release_id": self.release_id,
            "bundle": self.bundle,
            "manifest": self.manifest,
            "checksums": self.checksums,
            "bundle_sha256": self.bundle_sha256,
            "artifact": self.artifact,
            "release_set": self.release_set,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "BundleInfo":
        try:
            return cls(
                release_id=str(value["release_id"]),
                bundle=str(value["bundle"]),
                manifest=str(value["manifest"]),
                checksums=str(value["checksums"]),
                bundle_sha256=str(value["bundle_sha256"]),
                artifact=str(value.get("artifact", "full")),
                release_set=(
                    str(value["release_set"]) if value.get("release_set") else None
                ),
            )
        except (KeyError, TypeError, ValueError) as exc:
            raise DeployConfigError(f"invalid bundle information: {exc}") from exc


@dataclass(frozen=True)
class ReleaseArtifactRecord:
    name: str
    bundle: str
    bundle_sha256: str
    site_tree_sha256: str
    file_count: int
    total_bytes: int

    def __post_init__(self) -> None:
        if not ARTIFACT_NAME_RE.fullmatch(self.name):
            raise DeployConfigError("release set has an invalid artifact name")
        if not self.bundle or "/" in self.bundle or "\\" in self.bundle:
            raise DeployConfigError("release set bundle must be a plain file name")
        if not SHA256_RE.fullmatch(self.bundle_sha256):
            raise DeployConfigError("release set has an invalid bundle digest")
        if not SHA256_RE.fullmatch(self.site_tree_sha256):
            raise DeployConfigError("release set has an invalid site digest")
        if self.file_count < 1 or self.total_bytes < 1:
            raise DeployConfigError("release set artifact must contain files")

    def public_dict(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "bundle": self.bundle,
            "bundle_sha256": self.bundle_sha256,
            "site_tree_sha256": self.site_tree_sha256,
            "file_count": self.file_count,
            "total_bytes": self.total_bytes,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "ReleaseArtifactRecord":
        try:
            expected = {
                "name",
                "bundle",
                "bundle_sha256",
                "site_tree_sha256",
                "file_count",
                "total_bytes",
            }
            if set(value) != expected:
                raise DeployConfigError("release artifact fields are invalid")
            return cls(
                name=str(value["name"]),
                bundle=str(value["bundle"]),
                bundle_sha256=str(value["bundle_sha256"]),
                site_tree_sha256=str(value["site_tree_sha256"]),
                file_count=int(value["file_count"]),
                total_bytes=int(value["total_bytes"]),
            )
        except (KeyError, TypeError, ValueError) as exc:
            raise DeployConfigError(f"invalid release artifact: {exc}") from exc


@dataclass(frozen=True)
class ReleaseSetManifest:
    release_id: str
    spec_digest: str
    generated_at: str
    artifact_policy_sha256: str
    artifacts: tuple[ReleaseArtifactRecord, ...]

    def __post_init__(self) -> None:
        release_match = RELEASE_ID_RE.fullmatch(self.release_id)
        if not release_match:
            raise DeployConfigError("release set has an invalid release ID")
        if not SHA256_RE.fullmatch(self.spec_digest):
            raise DeployConfigError("release set has an invalid spec digest")
        if (
            release_match.group("digest")
            != self.spec_digest.removeprefix("sha256:")[:12]
        ):
            raise DeployConfigError("release set ID does not match its spec digest")
        if not SHA256_RE.fullmatch(self.artifact_policy_sha256):
            raise DeployConfigError("release set has an invalid policy digest")
        try:
            datetime.fromisoformat(self.generated_at.replace("Z", "+00:00"))
        except ValueError as exc:
            raise DeployConfigError(
                "release set generated_at must be an ISO timestamp"
            ) from exc
        names = [artifact.name for artifact in self.artifacts]
        if set(names) != {"full", "pages"} or len(names) != 2:
            raise DeployConfigError("release set must contain full and pages artifacts")
        for artifact in self.artifacts:
            suffix = (
                ".site.tar.zst"
                if artifact.name == "full"
                else f".{artifact.name}.site.tar.zst"
            )
            if artifact.bundle != f"{self.release_id}{suffix}":
                raise DeployConfigError(
                    f"release set has a non-canonical {artifact.name} bundle name"
                )

    def artifact(self, name: str) -> ReleaseArtifactRecord:
        for artifact in self.artifacts:
            if artifact.name == name:
                return artifact
        raise DeployConfigError(f"release set has no artifact named {name!r}")

    def public_dict(self) -> dict[str, Any]:
        return {
            "schema_version": 1,
            "release_id": self.release_id,
            "spec_digest": self.spec_digest,
            "generated_at": self.generated_at,
            "artifact_policy_sha256": self.artifact_policy_sha256,
            "artifacts": [artifact.public_dict() for artifact in self.artifacts],
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "ReleaseSetManifest":
        try:
            expected = {
                "schema_version",
                "release_id",
                "spec_digest",
                "generated_at",
                "artifact_policy_sha256",
                "artifacts",
            }
            if set(value) != expected or value.get("schema_version") != 1:
                raise DeployConfigError("release set fields are invalid")
            return cls(
                release_id=str(value["release_id"]),
                spec_digest=str(value["spec_digest"]),
                generated_at=str(value["generated_at"]),
                artifact_policy_sha256=str(value["artifact_policy_sha256"]),
                artifacts=tuple(
                    ReleaseArtifactRecord.from_dict(item)
                    for item in value["artifacts"]
                ),
            )
        except (KeyError, TypeError, ValueError) as exc:
            raise DeployConfigError(f"invalid release set: {exc}") from exc


@dataclass(frozen=True)
class ReleasePackageResult:
    """The two delivery artifacts bound to one immutable release set."""

    full: BundleInfo
    pages: BundleInfo
    release_set: ReleaseSetManifest

    def __post_init__(self) -> None:
        bundles = {self.full.artifact: self.full, self.pages.artifact: self.pages}
        if set(bundles) != {"full", "pages"}:
            raise DeployConfigError("release package requires full and pages bundles")
        if any(
            bundle.release_id != self.release_set.release_id
            for bundle in bundles.values()
        ):
            raise DeployConfigError("release package IDs do not agree")
        for name, bundle in bundles.items():
            record = self.release_set.artifact(name)
            if (
                record.bundle != Path(bundle.bundle).name
                or record.bundle_sha256 != bundle.bundle_sha256
            ):
                raise DeployConfigError(
                    f"release set does not bind the {name} bundle"
                )

    def public_dict(self) -> dict[str, Any]:
        return {
            "release_id": self.release_set.release_id,
            "artifacts": {
                "full": self.full.public_dict(),
                "pages": self.pages.public_dict(),
            },
            "release_set": self.release_set.public_dict(),
        }


__all__ = [
    "BranchBuildResult",
    "BundleInfo",
    "ReleaseBuildReport",
    "ReleaseArtifactRecord",
    "ReleaseManifest",
    "ReleasePackageResult",
    "ReleaseSetManifest",
    "StageOutcome",
]
