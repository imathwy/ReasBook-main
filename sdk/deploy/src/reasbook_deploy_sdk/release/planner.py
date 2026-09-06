"""Resolve release intent into immutable branch and project inputs."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
import hashlib
from typing import Iterable

from reasbook_build_sdk import (
    ConfigurationError,
    parse_library_declarations_text,
    parse_library_roots_text,
    target_from_declarations,
)

from ..errors import DeployConfigError
from ..git import version_key
from .models import (
    BranchSpec,
    CanonicalProjects,
    DeploymentProfile,
    ProjectSpec,
    ReleaseSpec,
    SourceProject,
    ToolchainRegistry,
)
from .ports import ReleaseSourcePort


@dataclass(frozen=True)
class _ResolvedBranch:
    spec: BranchSpec
    declarations: dict[str, str | None]
    roots: dict[str, tuple[str, ...]]
    projects: tuple[SourceProject, ...]


class ReleasePlanner:
    """Apply canonical and branch policy without starting any build."""

    def __init__(
        self,
        source: ReleaseSourcePort,
        *,
        resolved_at: datetime | None = None,
    ) -> None:
        self.source = source
        self.resolved_at = resolved_at

    def resolve(
        self,
        profile: DeploymentProfile,
        registry: ToolchainRegistry,
        canonical: CanonicalProjects,
        *,
        only: Iterable[str] = (),
    ) -> ReleaseSpec:
        selected_keys = {value.strip() for value in only if value.strip()}
        branches = tuple(
            self._resolve_branch(item.branch, expected_version=item.version)
            for item in sorted(
                registry.active(), key=lambda item: version_key(item.branch)
            )
        )
        occurrences: dict[str, list[tuple[_ResolvedBranch, SourceProject]]] = {}
        for branch in branches:
            for project in branch.projects:
                if project.key in profile.exclude:
                    continue
                if selected_keys and project.key not in selected_keys:
                    continue
                occurrences.setdefault(project.key, []).append((branch, project))
        if selected_keys:
            missing = sorted(selected_keys - set(occurrences))
            if missing:
                raise DeployConfigError(
                    f"selected projects were not found: {', '.join(missing)}"
                )
        if not occurrences:
            raise DeployConfigError("release selection contains no projects")

        project_specs: list[ProjectSpec] = []
        used_branches: dict[str, BranchSpec] = {}
        for key, versions in sorted(occurrences.items()):
            canonical_branch = self._canonical_branch(key, versions, canonical)
            for branch, project in versions:
                is_canonical = branch.spec.name == canonical_branch
                if (not profile.include_historical_versions or profile.selection_mode == "canonical") and not is_canonical:
                    continue
                try:
                    target = target_from_declarations(
                        branch.declarations,
                        project.project_id,
                        "book" if project.kind == "books" else "paper",
                        roots=branch.roots,
                    )
                except ConfigurationError as exc:
                    raise DeployConfigError(
                        f"cannot resolve build target for {key} on "
                        f"{branch.spec.name}: {exc}"
                    ) from exc
                used_branches[branch.spec.name] = branch.spec
                project_specs.append(
                    ProjectSpec(
                        key=key,
                        kind=project.kind,
                        project_id=project.project_id,
                        slug=project.slug,
                        branch=branch.spec.name,
                        commit=branch.spec.commit,
                        source_path=project.source_path,
                        build_target=target,
                        canonical=is_canonical,
                        outputs=profile.policy.outputs(),
                    )
                )

        return ReleaseSpec.create(
            repository=self.source.repository_url(),
            registry_commit=self.source.registry_commit(),
            tooling_revision=self.source.tooling_revision(),
            base_path=profile.base_path,
            include_historical_versions=profile.include_historical_versions,
            policy=profile.policy,
            branches=used_branches.values(),
            projects=project_specs,
            resolved_at=self.resolved_at,
        )

    def _resolve_branch(
        self,
        branch: str,
        *,
        expected_version: str,
    ) -> _ResolvedBranch:
        commit = self.source.branch_commit(branch)
        toolchain = self.source.read_text(branch, "ReasBook/lean-toolchain").strip()
        actual_version = toolchain.rsplit(":", 1)[-1]
        if actual_version != expected_version:
            raise DeployConfigError(
                f"{branch} toolchain {actual_version!r} does not match "
                f"registered version {expected_version!r}"
            )
        manifest = self.source.read_text(branch, "ReasBook/lake-manifest.json")
        lakefile = self.source.read_text(branch, "ReasBook/lakefile.lean")
        digest = hashlib.sha256(manifest.encode("utf-8")).hexdigest()
        return _ResolvedBranch(
            spec=BranchSpec(
                name=branch,
                commit=commit,
                toolchain=toolchain,
                lake_manifest_sha256=f"sha256:{digest}",
            ),
            declarations=parse_library_declarations_text(lakefile),
            roots=parse_library_roots_text(lakefile),
            projects=tuple(self.source.discover_projects(branch)),
        )

    @staticmethod
    def _canonical_branch(
        key: str,
        versions: list[tuple[_ResolvedBranch, SourceProject]],
        canonical: CanonicalProjects,
    ) -> str:
        available = {branch.spec.name for branch, _ in versions}
        configured = canonical.get(key)
        if configured is None:
            if len(available) > 1:
                raise DeployConfigError(
                    f"{key} exists on multiple branches and needs an explicit "
                    "canonical version"
                )
            return next(iter(available))
        if configured not in available:
            raise DeployConfigError(
                f"canonical branch {configured} for {key} is unavailable; "
                f"available: {', '.join(sorted(available, key=version_key))}"
            )
        return configured


__all__ = ["ReleasePlanner"]
