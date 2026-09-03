"""Build evidence and portable release-manifest models."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from ..errors import DeployConfigError
from .models import ReleaseSpec, SHA256_RE


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

    def __post_init__(self) -> None:
        if self.status not in {"success", "degraded"}:
            raise DeployConfigError("only a successful build can be packaged")
        if not SHA256_RE.fullmatch(self.spec_digest):
            raise DeployConfigError("release manifest has an invalid spec digest")
        if not SHA256_RE.fullmatch(self.site_tree_sha256):
            raise DeployConfigError("release manifest has an invalid site digest")
        if self.file_count < 1 or self.total_bytes < 1:
            raise DeployConfigError("release site must contain files")
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
            "schema_version": 1,
            "release_id": self.release_id,
            "spec_digest": self.spec_digest,
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
            expected = {
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
            if set(value) != expected or value.get("schema_version") != 1:
                raise DeployConfigError(
                    "release manifest fields do not match schema version 1"
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

    def __post_init__(self) -> None:
        if not SHA256_RE.fullmatch(self.bundle_sha256):
            raise DeployConfigError("bundle checksum is invalid")

    def public_dict(self) -> dict[str, str]:
        return {
            "release_id": self.release_id,
            "bundle": self.bundle,
            "manifest": self.manifest,
            "checksums": self.checksums,
            "bundle_sha256": self.bundle_sha256,
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
            )
        except (KeyError, TypeError, ValueError) as exc:
            raise DeployConfigError(f"invalid bundle information: {exc}") from exc


__all__ = [
    "BranchBuildResult",
    "BundleInfo",
    "ReleaseBuildReport",
    "ReleaseManifest",
    "StageOutcome",
]
