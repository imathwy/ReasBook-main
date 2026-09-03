"""Pure branch command planning for a local static release."""

from __future__ import annotations

from dataclasses import dataclass
import math
from pathlib import Path
import re
from typing import Mapping

from ..errors import DeployExecutionError
from ..runtime import safe_name
from .models import BranchSpec, ProjectSpec, ReleaseSpec
from .store import ReleaseLayout


@dataclass(frozen=True)
class ReleaseBuildOptions:
    max_parallel_branches: int = 2
    build_timeout_seconds: float = 21600.0
    docs_timeout_seconds: float = 21600.0
    verso_timeout_seconds: float = 21600.0
    graph_timeout_seconds: float = 3600.0

    def __post_init__(self) -> None:
        if (
            isinstance(self.max_parallel_branches, bool)
            or not isinstance(self.max_parallel_branches, int)
            or self.max_parallel_branches < 1
        ):
            raise DeployExecutionError("max_parallel_branches must be positive")
        for name, value in (
            ("build timeout", self.build_timeout_seconds),
            ("docs timeout", self.docs_timeout_seconds),
            ("Verso timeout", self.verso_timeout_seconds),
            ("graph timeout", self.graph_timeout_seconds),
        ):
            if not math.isfinite(value) or value <= 0:
                raise DeployExecutionError(f"{name} must be positive")


@dataclass(frozen=True)
class BranchStep:
    name: str
    argv: tuple[str, ...]
    cwd: Path
    env: tuple[tuple[str, str], ...]
    timeout: float
    required: bool = True

    def public_dict(self) -> dict[str, object]:
        return {
            "name": self.name,
            "argv": list(self.argv),
            "cwd": str(self.cwd),
            "environment_keys": [key for key, _ in self.env],
            "timeout_seconds": self.timeout,
            "required": self.required,
        }


@dataclass(frozen=True)
class BranchBuildPlan:
    branch: BranchSpec
    worktree: Path
    projects: tuple[ProjectSpec, ...]
    steps: tuple[BranchStep, ...]
    source_site: Path
    published_site: Path

    def public_dict(self) -> dict[str, object]:
        return {
            "branch": self.branch.public_dict(),
            "worktree": str(self.worktree),
            "projects": [project.key for project in self.projects],
            "steps": [step.public_dict() for step in self.steps],
            "source_site": str(self.source_site),
            "published_site": str(self.published_site),
        }


class BranchPlanFactory:
    """Translate one branch spec into repository-adapter commands."""

    def __init__(
        self,
        tooling_root: Path,
        cache_root: Path,
        layout: ReleaseLayout,
        options: ReleaseBuildOptions,
    ) -> None:
        self.tooling_root = Path(tooling_root).expanduser().resolve()
        self.cache_root = Path(cache_root).expanduser().resolve()
        self.layout = layout
        self.options = options

    def create(
        self,
        spec: ReleaseSpec,
        branch: BranchSpec,
        worktree: Path,
    ) -> BranchBuildPlan:
        projects = tuple(
            project for project in spec.projects if project.branch == branch.name
        )
        if not projects:
            raise DeployExecutionError(f"release branch has no projects: {branch.name}")
        environment = self._environment(spec, branch, projects, worktree)
        steps = self._steps(spec, branch, projects, worktree, environment)
        return BranchBuildPlan(
            branch=branch,
            worktree=worktree,
            projects=projects,
            steps=steps,
            source_site=worktree / "ReasBookWeb" / "_site",
            published_site=(self.layout.branch_sites / safe_name(branch.name) / "site"),
        )

    def _environment(
        self,
        spec: ReleaseSpec,
        branch: BranchSpec,
        projects: tuple[ProjectSpec, ...],
        worktree: Path,
    ) -> dict[str, str]:
        environment = {
            "REASBOOK_REPO_ROOT": str(worktree),
            "REASBOOK_CACHE_ROOT": str(self.cache_root),
            "REASBOOK_RUNTIME_CACHE_PREFIX": (
                f"branch-{safe_name(branch.name)}-{branch.commit[:12]}-"
                f"{branch.lake_manifest_sha256.removeprefix('sha256:')[:12]}-"
            ),
            "MATHLIB_CACHE_DIR": str(
                self.cache_root
                / "mathlib"
                / "releases"
                / safe_name(branch.toolchain.rsplit(":", 1)[-1])
            ),
            "REASBOOK_GITHUB_BRANCH": branch.name,
            "REASBOOK_SITE_ROOT": (
                f"{spec.base_path.rstrip('/')}/versions/{branch.name}/"
                if spec.include_historical_versions
                else spec.base_path
            ),
            "REASBOOK_LAKE_TARGETS": ",".join(
                project.build_target for project in projects
            ),
            "REASBOOK_INCLUDE_PROJECTS": ",".join(project.key for project in projects),
            "REASBOOK_VERSO_GENERATOR": str(
                self.tooling_root / "ReasBookWeb" / "scripts" / "gen_sections.py"
            ),
        }
        github = re.match(
            r"^https://github[.]com/(?P<owner>[^/]+)/(?P<repo>[^/]+?)(?:[.]git)?$",
            spec.repository,
        )
        if github:
            environment["REASBOOK_SITE_BASE"] = (
                f"https://{github.group('owner')}.github.io"
                f"{environment['REASBOOK_SITE_ROOT']}"
            )
        return environment

    def _steps(
        self,
        spec: ReleaseSpec,
        branch: BranchSpec,
        projects: tuple[ProjectSpec, ...],
        worktree: Path,
        environment: dict[str, str],
    ) -> tuple[BranchStep, ...]:
        scripts = self.tooling_root / "scripts" / "build"
        steps = [
            self._step(
                "cache",
                (str(scripts / "cache.sh"),),
                worktree,
                environment,
                self.options.build_timeout_seconds,
                required=False,
            )
        ]
        if spec.policy.require_lean:
            steps.append(
                self._step(
                    "lean",
                    (str(scripts / "core.sh"),),
                    worktree,
                    environment,
                    self.options.build_timeout_seconds,
                )
            )
        if spec.policy.require_docs:
            steps.extend(
                self._docs_steps(projects, worktree, environment, scripts, spec)
            )
        if spec.policy.require_verso:
            steps.append(
                self._step(
                    "verso",
                    (str(scripts / "verso.sh"),),
                    worktree,
                    environment,
                    self.options.verso_timeout_seconds,
                )
            )
        if spec.policy.require_docs:
            steps.append(
                self._step(
                    "publish-docs",
                    (str(scripts / "publish_docs.sh"),),
                    worktree,
                    environment,
                    self.options.docs_timeout_seconds,
                    required=not spec.policy.allow_partial,
                )
            )
        if spec.policy.theorem_graph != "none":
            steps.append(
                self._graph_step(
                    spec,
                    branch,
                    projects,
                    worktree,
                    environment,
                )
            )
        return tuple(steps)

    def _docs_steps(
        self,
        projects: tuple[ProjectSpec, ...],
        worktree: Path,
        environment: dict[str, str],
        scripts: Path,
        spec: ReleaseSpec,
    ) -> list[BranchStep]:
        return [
            self._step(
                f"docs-{project.slug}",
                (str(scripts / "project_docs.sh"),),
                worktree,
                {
                    **environment,
                    "PROJECT_DOC_MODULES": project.build_target,
                },
                self.options.docs_timeout_seconds,
                required=not spec.policy.allow_partial,
            )
            for project in projects
        ]

    def _graph_step(
        self,
        spec: ReleaseSpec,
        branch: BranchSpec,
        projects: tuple[ProjectSpec, ...],
        worktree: Path,
        environment: dict[str, str],
    ) -> BranchStep:
        argv = [
            str(self.tooling_root / "sdk" / "theorem_graph" / "bin" / "theorem-graph"),
            "--repo-root",
            str(worktree),
            "--site-root",
            str(worktree / "ReasBookWeb" / "_site"),
            "--branch",
            branch.name,
            "--include-generic",
        ]
        if spec.policy.theorem_graph == "compiled":
            argv.append("--no-source-fallback")
        elif spec.policy.theorem_graph == "source":
            argv.append("--source-only")
        for project in projects:
            argv.extend(("--project", project.key))
        return self._step(
            "theorem-graph",
            tuple(argv),
            worktree,
            environment,
            self.options.graph_timeout_seconds,
            required=not spec.policy.allow_partial,
        )

    @staticmethod
    def _step(
        name: str,
        argv: tuple[str, ...],
        cwd: Path,
        env: Mapping[str, str],
        timeout: float,
        *,
        required: bool = True,
    ) -> BranchStep:
        return BranchStep(
            name,
            argv,
            cwd,
            tuple(sorted(env.items())),
            timeout,
            required,
        )


__all__ = [
    "BranchBuildPlan",
    "BranchPlanFactory",
    "BranchStep",
    "ReleaseBuildOptions",
]
