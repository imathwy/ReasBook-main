"""Pure value objects for a reproducible static-site release."""

from __future__ import annotations

from dataclasses import dataclass, field
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
from typing import Any, Iterable, Mapping

from ..errors import DeployConfigError


BRANCH_RE = re.compile(r"^v\d+\.\d+\.\d+$")
COMMIT_RE = re.compile(r"^[0-9a-f]{40,64}$")
PROJECT_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]{0,160}$")
PROJECT_KEY_RE = re.compile(
    r"^(?P<kind>books|papers)/(?P<project>[A-Za-z0-9][A-Za-z0-9_.-]{0,160})$"
)
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
RELEASE_ID_RE = re.compile(r"^site-\d{8}T\d{6}Z-(?P<digest>[0-9a-f]{12})$")
ARTIFACT_NAME_RE = re.compile(r"^[a-z][a-z0-9_-]{0,31}$")
GITHUB_PAGES_HARD_SITE_BYTES = 1_000_000_000


def _text(value: object, *, field: str) -> str:
    if value is None:
        raise DeployConfigError(f"{field} must be a non-empty safe string")
    result = str(value).strip()
    if not result or any(char in result for char in "\x00\r\n"):
        raise DeployConfigError(f"{field} must be a non-empty safe string")
    return result


def _base_path(value: object) -> str:
    path = _text(value, field="site.base_path")
    if not path.startswith("/"):
        path = f"/{path}"
    if not path.endswith("/"):
        path = f"{path}/"
    if "//" in path or ".." in path:
        raise DeployConfigError("site.base_path contains an unsafe component")
    return path


def _project_key(kind: str, project: str) -> str:
    normalized = kind.strip().lower()
    if normalized not in {"books", "papers"}:
        raise DeployConfigError(f"unsupported project kind: {kind!r}")
    if not PROJECT_ID_RE.fullmatch(project):
        raise DeployConfigError(f"unsafe project ID: {project!r}")
    return f"{normalized}/{project}"


def _version_key(value: str) -> tuple[int, int, int, str]:
    match = re.fullmatch(r"v(\d+)\.(\d+)\.(\d+)", value)
    if not match:
        return (-1, -1, -1, value)
    return (
        int(match.group(1)),
        int(match.group(2)),
        int(match.group(3)),
        value,
    )


@dataclass(frozen=True)
class ReleasePolicy:
    allow_partial: bool = False
    require_lean: bool = True
    require_docs: bool = True
    require_verso: bool = True
    theorem_graph: str = "compiled_or_source"
    max_site_files: int = 100000
    max_bundle_bytes: int = 1900000000

    def __post_init__(self) -> None:
        for name, value in (
            ("allow_partial", self.allow_partial),
            ("require_lean", self.require_lean),
            ("require_docs", self.require_docs),
            ("require_verso", self.require_verso),
        ):
            if not isinstance(value, bool):
                raise DeployConfigError(f"policy.{name} must be boolean")
        if self.theorem_graph not in {
            "none",
            "source",
            "compiled",
            "compiled_or_source",
        }:
            raise DeployConfigError(
                "policy.theorem_graph must be none, source, compiled, "
                "or compiled_or_source"
            )
        for name, value in (
            ("max_site_files", self.max_site_files),
            ("max_bundle_bytes", self.max_bundle_bytes),
        ):
            if isinstance(value, bool) or not isinstance(value, int) or value < 1:
                raise DeployConfigError(f"policy.{name} must be a positive integer")

    def outputs(self) -> tuple[str, ...]:
        values: list[str] = []
        if self.require_lean:
            values.append("lean")
        if self.require_docs:
            values.append("docs")
        if self.require_verso:
            values.append("verso")
        if self.theorem_graph != "none":
            values.append("theorem_graph")
        return tuple(values)

    def public_dict(self) -> dict[str, Any]:
        return {
            "allow_partial": self.allow_partial,
            "require_lean": self.require_lean,
            "require_docs": self.require_docs,
            "require_verso": self.require_verso,
            "theorem_graph": self.theorem_graph,
            "max_site_files": self.max_site_files,
            "max_bundle_bytes": self.max_bundle_bytes,
        }


@dataclass(frozen=True)
class GitHubPublishProfile:
    repository: str
    release_tag_prefix: str = "reasbook-site"
    workflow: str = "publish_release_pages.yml"

    def __post_init__(self) -> None:
        repository = _text(self.repository, field="publish.repository")
        if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository):
            raise DeployConfigError(
                "publish.repository must look like owner/repository"
            )
        prefix = _text(self.release_tag_prefix, field="publish.release_tag_prefix")
        if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]*", prefix):
            raise DeployConfigError("publish.release_tag_prefix is unsafe")
        workflow = _text(self.workflow, field="publish.workflow")
        if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*\.(?:yml|yaml)", workflow):
            raise DeployConfigError(
                "publish.workflow must be a plain YAML workflow file name"
            )

    def public_dict(self) -> dict[str, str]:
        return {
            "adapter": "github_pages",
            "repository": self.repository,
            "release_tag_prefix": self.release_tag_prefix,
            "workflow": self.workflow,
        }


@dataclass(frozen=True)
class ReleaseArtifactPolicy:
    """Content and capacity contract for one immutable release artifact."""

    name: str
    history_mode: str
    dependency_docs: str
    max_site_files: int
    max_site_bytes: int
    max_archive_members: int
    max_bundle_bytes: int

    def __post_init__(self) -> None:
        if not ARTIFACT_NAME_RE.fullmatch(self.name):
            raise DeployConfigError(f"invalid release artifact name: {self.name!r}")
        if self.history_mode not in {"full", "canonical"}:
            raise DeployConfigError(
                f"artifacts.{self.name}.history_mode must be full or canonical"
            )
        if self.dependency_docs not in {"full", "stubs"}:
            raise DeployConfigError(
                f"artifacts.{self.name}.dependency_docs must be full or stubs"
            )
        for field_name, value in (
            ("max_site_files", self.max_site_files),
            ("max_site_bytes", self.max_site_bytes),
            ("max_archive_members", self.max_archive_members),
            ("max_bundle_bytes", self.max_bundle_bytes),
        ):
            if isinstance(value, bool) or not isinstance(value, int) or value < 1:
                raise DeployConfigError(
                    f"artifacts.{self.name}.{field_name} must be a positive integer"
                )

    def public_dict(self) -> dict[str, Any]:
        return {
            "history_mode": self.history_mode,
            "dependency_docs": self.dependency_docs,
            "max_site_files": self.max_site_files,
            "max_site_bytes": self.max_site_bytes,
            "max_archive_members": self.max_archive_members,
            "max_bundle_bytes": self.max_bundle_bytes,
        }


def default_artifact_policies() -> tuple[ReleaseArtifactPolicy, ...]:
    """Return conservative defaults for pre-ReleaseSet profile snapshots."""

    return (
        ReleaseArtifactPolicy(
            name="full",
            history_mode="full",
            dependency_docs="stubs",
            max_site_files=500_000,
            max_site_bytes=100_000_000_000,
            max_archive_members=1_501_024,
            max_bundle_bytes=20_000_000_000,
        ),
        ReleaseArtifactPolicy(
            name="pages",
            history_mode="canonical",
            dependency_docs="stubs",
            max_site_files=60_000,
            max_site_bytes=920_000_000,
            max_archive_members=180_000,
            max_bundle_bytes=950_000_000,
        ),
    )


@dataclass(frozen=True)
class DeploymentProfile:
    name: str
    registry: Path
    canonical_projects: Path
    base_path: str
    include_historical_versions: bool
    policy: ReleasePolicy
    publish: GitHubPublishProfile
    exclude: tuple[str, ...] = ()
    artifacts: tuple[ReleaseArtifactPolicy, ...] = field(
        default_factory=default_artifact_policies
    )

    def __post_init__(self) -> None:
        _text(self.name, field="profile.name")
        if not isinstance(self.include_historical_versions, bool):
            raise DeployConfigError("site.include_historical_versions must be boolean")
        object.__setattr__(self, "base_path", _base_path(self.base_path))
        for key in self.exclude:
            if not PROJECT_KEY_RE.fullmatch(key):
                raise DeployConfigError(f"invalid excluded project key: {key!r}")
        names = [artifact.name for artifact in self.artifacts]
        if len(set(names)) != len(names):
            raise DeployConfigError("profile contains duplicate artifact policies")
        if set(names) != {"full", "pages"}:
            raise DeployConfigError(
                "profile must define exactly the full and pages artifacts"
            )
        full = self.artifact("full")
        pages = self.artifact("pages")
        if (full.history_mode, full.dependency_docs) != ("full", "stubs"):
            raise DeployConfigError(
                "the full artifact must retain full history and explicit "
                "dependency-doc stubs"
            )
        if (pages.history_mode, pages.dependency_docs) != (
            "canonical",
            "stubs",
        ):
            raise DeployConfigError(
                "the pages artifact must retain canonical history and stub "
                "dependency docs"
            )
        if pages.max_site_bytes > GITHUB_PAGES_HARD_SITE_BYTES:
            raise DeployConfigError(
                "the pages artifact operational budget cannot exceed the "
                f"GitHub Pages hard limit of {GITHUB_PAGES_HARD_SITE_BYTES} bytes"
            )

    def artifact(self, name: str) -> ReleaseArtifactPolicy:
        for artifact in self.artifacts:
            if artifact.name == name:
                return artifact
        raise DeployConfigError(f"profile has no artifact named {name!r}")


@dataclass(frozen=True)
class RegistryBranch:
    version: str
    branch: str
    status: str

    def __post_init__(self) -> None:
        if not BRANCH_RE.fullmatch(self.version):
            raise DeployConfigError(f"invalid registered version: {self.version!r}")
        if not BRANCH_RE.fullmatch(self.branch):
            raise DeployConfigError(f"invalid registered branch: {self.branch!r}")
        if self.status not in {"active", "frozen", "archived", "empty"}:
            raise DeployConfigError(f"invalid branch status: {self.status!r}")


@dataclass(frozen=True)
class ToolchainRegistry:
    branches: tuple[RegistryBranch, ...]

    def active(self) -> tuple[RegistryBranch, ...]:
        return tuple(
            branch for branch in self.branches if branch.status in {"active", "frozen"}
        )


@dataclass(frozen=True)
class CanonicalProjects:
    entries: tuple[tuple[str, str], ...]

    def __post_init__(self) -> None:
        seen: set[str] = set()
        for key, branch in self.entries:
            if not PROJECT_KEY_RE.fullmatch(key):
                raise DeployConfigError(f"invalid canonical project key: {key!r}")
            if not BRANCH_RE.fullmatch(branch):
                raise DeployConfigError(f"invalid canonical branch: {branch!r}")
            if key in seen:
                raise DeployConfigError(f"duplicate canonical project key: {key}")
            seen.add(key)

    def get(self, key: str) -> str | None:
        return dict(self.entries).get(key)

    def public_dict(self) -> dict[str, str]:
        return dict(self.entries)


@dataclass(frozen=True)
class SourceProject:
    kind: str
    project_id: str

    def __post_init__(self) -> None:
        _project_key(self.kind, self.project_id)

    @property
    def key(self) -> str:
        return _project_key(self.kind, self.project_id)

    @property
    def slug(self) -> str:
        return self.project_id.lower()

    @property
    def source_path(self) -> str:
        kind_dir = "Books" if self.kind == "books" else "Papers"
        return f"ReasBook/{kind_dir}/{self.project_id}"


@dataclass(frozen=True)
class BranchSpec:
    name: str
    commit: str
    toolchain: str
    lake_manifest_sha256: str

    def __post_init__(self) -> None:
        if not BRANCH_RE.fullmatch(self.name):
            raise DeployConfigError(f"invalid release branch: {self.name!r}")
        if not COMMIT_RE.fullmatch(self.commit):
            raise DeployConfigError(f"invalid commit for {self.name}: {self.commit!r}")
        _text(self.toolchain, field=f"{self.name}.toolchain")
        if not SHA256_RE.fullmatch(self.lake_manifest_sha256):
            raise DeployConfigError(f"invalid Lake manifest digest for {self.name}")

    def public_dict(self) -> dict[str, str]:
        return {
            "name": self.name,
            "commit": self.commit,
            "toolchain": self.toolchain,
            "lake_manifest_sha256": self.lake_manifest_sha256,
        }


@dataclass(frozen=True)
class ProjectSpec:
    key: str
    kind: str
    project_id: str
    slug: str
    branch: str
    commit: str
    source_path: str
    build_target: str
    canonical: bool
    outputs: tuple[str, ...]

    def __post_init__(self) -> None:
        if self.key != _project_key(self.kind, self.project_id):
            raise DeployConfigError(f"project key does not match kind/id: {self.key}")
        if not BRANCH_RE.fullmatch(self.branch):
            raise DeployConfigError(f"invalid project branch: {self.branch!r}")
        if not COMMIT_RE.fullmatch(self.commit):
            raise DeployConfigError(f"invalid project commit: {self.commit!r}")
        if not isinstance(self.canonical, bool):
            raise DeployConfigError(f"{self.key}.canonical must be boolean")
        _text(self.build_target, field=f"{self.key}.build_target")
        if self.slug != self.project_id.lower():
            raise DeployConfigError(f"invalid project slug for {self.key}")
        expected_source = SourceProject(self.kind, self.project_id).source_path
        if self.source_path != expected_source:
            raise DeployConfigError(f"invalid source path for {self.key}")
        allowed = {"lean", "docs", "verso", "theorem_graph"}
        if (
            not self.outputs
            or len(set(self.outputs)) != len(self.outputs)
            or any(value not in allowed for value in self.outputs)
        ):
            raise DeployConfigError(f"invalid outputs for {self.key}")

    def public_dict(self) -> dict[str, Any]:
        return {
            "key": self.key,
            "kind": self.kind,
            "project_id": self.project_id,
            "slug": self.slug,
            "branch": self.branch,
            "commit": self.commit,
            "source_path": self.source_path,
            "build_target": self.build_target,
            "canonical": self.canonical,
            "outputs": list(self.outputs),
        }


@dataclass(frozen=True)
class ReleaseSpec:
    release_id: str
    spec_digest: str
    resolved_at: str
    repository: str
    registry_commit: str
    tooling_revision: str
    base_path: str
    include_historical_versions: bool
    policy: ReleasePolicy
    branches: tuple[BranchSpec, ...]
    projects: tuple[ProjectSpec, ...]

    def __post_init__(self) -> None:
        release_match = RELEASE_ID_RE.fullmatch(self.release_id)
        if not release_match:
            raise DeployConfigError("release_id has an invalid format")
        if not SHA256_RE.fullmatch(self.spec_digest):
            raise DeployConfigError("spec_digest must be a sha256 digest")
        if (
            release_match.group("digest")
            != self.spec_digest.removeprefix("sha256:")[:12]
        ):
            raise DeployConfigError("release_id does not match spec_digest")
        _text(self.repository, field="source.repository")
        if not COMMIT_RE.fullmatch(self.registry_commit):
            raise DeployConfigError("source.registry_commit must be a Git commit")
        tooling_revision = _text(
            self.tooling_revision,
            field="source.tooling_revision",
        )
        if tooling_revision.split("+", 1)[0] != self.registry_commit:
            raise DeployConfigError(
                "source.tooling_revision must derive from source.registry_commit"
            )
        if not isinstance(self.include_historical_versions, bool):
            raise DeployConfigError("site.include_historical_versions must be boolean")
        object.__setattr__(self, "base_path", _base_path(self.base_path))
        try:
            datetime.fromisoformat(self.resolved_at.replace("Z", "+00:00"))
        except ValueError as exc:
            raise DeployConfigError("resolved_at must be an ISO timestamp") from exc
        if not self.branches or not self.projects:
            raise DeployConfigError("ReleaseSpec must contain branches and projects")
        branch_names = {branch.name for branch in self.branches}
        if len(branch_names) != len(self.branches):
            raise DeployConfigError("ReleaseSpec contains duplicate branches")
        if any(project.branch not in branch_names for project in self.projects):
            raise DeployConfigError("ReleaseSpec project references an unknown branch")
        by_key: dict[str, list[ProjectSpec]] = {}
        identities: set[tuple[str, str]] = set()
        for project in self.projects:
            identity = (project.key, project.branch)
            if identity in identities:
                raise DeployConfigError(
                    f"ReleaseSpec contains duplicate project version: "
                    f"{project.key}@{project.branch}"
                )
            identities.add(identity)
            by_key.setdefault(project.key, []).append(project)
        for key, versions in by_key.items():
            if sum(project.canonical for project in versions) != 1:
                raise DeployConfigError(
                    f"ReleaseSpec requires exactly one canonical version for {key}"
                )

    @classmethod
    def create(
        cls,
        *,
        repository: str,
        registry_commit: str,
        tooling_revision: str,
        base_path: str,
        include_historical_versions: bool,
        policy: ReleasePolicy,
        branches: Iterable[BranchSpec],
        projects: Iterable[ProjectSpec],
        resolved_at: datetime | None = None,
    ) -> "ReleaseSpec":
        branch_values = tuple(
            sorted(branches, key=lambda item: _version_key(item.name))
        )
        project_values = tuple(
            sorted(projects, key=lambda item: (item.key, item.branch))
        )
        payload = cls.digest_payload_for(
            repository=repository,
            registry_commit=registry_commit,
            tooling_revision=tooling_revision,
            base_path=_base_path(base_path),
            include_historical_versions=include_historical_versions,
            policy=policy,
            branches=branch_values,
            projects=project_values,
        )
        encoded = json.dumps(
            payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
        digest = hashlib.sha256(encoded).hexdigest()
        now = resolved_at or datetime.now(timezone.utc)
        timestamp = now.astimezone(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        return cls(
            release_id=f"site-{timestamp}-{digest[:12]}",
            spec_digest=f"sha256:{digest}",
            resolved_at=now.astimezone(timezone.utc)
            .isoformat(timespec="seconds")
            .replace("+00:00", "Z"),
            repository=repository,
            registry_commit=registry_commit,
            tooling_revision=tooling_revision,
            base_path=base_path,
            include_historical_versions=include_historical_versions,
            policy=policy,
            branches=branch_values,
            projects=project_values,
        )

    @staticmethod
    def digest_payload_for(
        *,
        repository: str,
        registry_commit: str,
        tooling_revision: str,
        base_path: str,
        include_historical_versions: bool,
        policy: ReleasePolicy,
        branches: tuple[BranchSpec, ...],
        projects: tuple[ProjectSpec, ...],
    ) -> dict[str, Any]:
        return {
            "schema_version": 1,
            "source": {
                "repository": repository,
                "registry_commit": registry_commit,
                "tooling_revision": tooling_revision,
            },
            "site": {
                "base_path": base_path,
                "include_historical_versions": include_historical_versions,
            },
            "policy": policy.public_dict(),
            "branches": [branch.public_dict() for branch in branches],
            "projects": [project.public_dict() for project in projects],
        }

    def public_dict(self) -> dict[str, Any]:
        payload = self.digest_payload_for(
            repository=self.repository,
            registry_commit=self.registry_commit,
            tooling_revision=self.tooling_revision,
            base_path=self.base_path,
            include_historical_versions=self.include_historical_versions,
            policy=self.policy,
            branches=self.branches,
            projects=self.projects,
        )
        return {
            "schema_version": 1,
            "release_id": self.release_id,
            "spec_digest": self.spec_digest,
            "resolved_at": self.resolved_at,
            **payload,
        }

    def branch(self, name: str) -> BranchSpec:
        for branch in self.branches:
            if branch.name == name:
                return branch
        raise DeployConfigError(f"ReleaseSpec has no branch {name}")

    def canonical_projects(self) -> tuple[ProjectSpec, ...]:
        return tuple(project for project in self.projects if project.canonical)

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "ReleaseSpec":
        try:
            expected_root = {
                "schema_version",
                "release_id",
                "spec_digest",
                "resolved_at",
                "source",
                "site",
                "policy",
                "branches",
                "projects",
            }
            if set(payload) != expected_root or payload.get("schema_version") != 1:
                raise DeployConfigError(
                    "ReleaseSpec root fields do not match schema version 1"
                )
            source = payload["source"]
            site = payload["site"]
            if not isinstance(source, Mapping) or set(source) != {
                "repository",
                "registry_commit",
                "tooling_revision",
            }:
                raise DeployConfigError("ReleaseSpec source fields are invalid")
            if not isinstance(site, Mapping) or set(site) != {
                "base_path",
                "include_historical_versions",
            }:
                raise DeployConfigError("ReleaseSpec site fields are invalid")
            policy_value = payload["policy"]
            policy = ReleasePolicy(**dict(policy_value))
            branches = tuple(BranchSpec(**dict(item)) for item in payload["branches"])
            projects = tuple(
                ProjectSpec(
                    **{
                        **dict(item),
                        "outputs": tuple(item["outputs"]),
                    }
                )
                for item in payload["projects"]
            )
            spec = cls(
                release_id=str(payload["release_id"]),
                spec_digest=str(payload["spec_digest"]),
                resolved_at=str(payload["resolved_at"]),
                repository=str(source["repository"]),
                registry_commit=str(source["registry_commit"]),
                tooling_revision=str(source["tooling_revision"]),
                base_path=str(site["base_path"]),
                include_historical_versions=site["include_historical_versions"],
                policy=policy,
                branches=branches,
                projects=projects,
            )
            encoded = json.dumps(
                spec.digest_payload_for(
                    repository=spec.repository,
                    registry_commit=spec.registry_commit,
                    tooling_revision=spec.tooling_revision,
                    base_path=spec.base_path,
                    include_historical_versions=spec.include_historical_versions,
                    policy=spec.policy,
                    branches=spec.branches,
                    projects=spec.projects,
                ),
                ensure_ascii=True,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
            expected = f"sha256:{hashlib.sha256(encoded).hexdigest()}"
            if spec.spec_digest != expected:
                raise DeployConfigError(
                    "ReleaseSpec digest does not match its immutable inputs"
                )
            return spec
        except (KeyError, TypeError, ValueError) as exc:
            raise DeployConfigError(f"invalid ReleaseSpec: {exc}") from exc
