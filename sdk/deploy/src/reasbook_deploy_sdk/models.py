"""Immutable configuration and result models for deployment orchestration."""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from pathlib import Path
import re
from typing import Any

from .errors import DeployConfigError


@dataclass(frozen=True)
class DeploymentConfig:
    """Inputs for a selected-book reviewer deployment.

    The model contains policy, not process details.  Git, cache, reviewer,
    and build adapters receive this object and remain independently testable.
    """

    repo_root: Path
    reviewer_root: Path
    data_root: Path
    cache_root: Path
    books: tuple[str, ...] = ()
    branch: str | None = None
    stacks_root: Path | None = None
    include_papers: bool = False
    build: bool = True
    build_docs: bool = False
    skip_cache: bool = False
    build_stacks: bool = False
    stacks_max_items: int = 0
    dry_run: bool = False
    serve: bool = False
    host: str = "127.0.0.1"
    port: int = 8876
    python_bin: str | None = None
    lake_bin: str | None = None

    def resolved(self) -> "DeploymentConfig":
        """Resolve paths and validate cross-root safety constraints."""

        def resolve(value: Path) -> Path:
            return Path(value).expanduser().resolve()

        try:
            port = int(self.port)
            stacks_max_items = int(self.stacks_max_items)
        except (TypeError, ValueError) as exc:
            raise DeployConfigError("port and stacks_max_items must be integers") from exc
        config = DeploymentConfig(
            repo_root=resolve(self.repo_root),
            reviewer_root=resolve(self.reviewer_root),
            data_root=resolve(self.data_root),
            cache_root=resolve(self.cache_root),
            books=tuple(self.books),
            branch=self.branch.strip() if self.branch else None,
            stacks_root=resolve(self.stacks_root) if self.stacks_root else None,
            include_papers=bool(self.include_papers),
            build=bool(self.build),
            build_docs=bool(self.build_docs and self.build),
            skip_cache=bool(self.skip_cache),
            build_stacks=bool(self.build_stacks and self.build),
            stacks_max_items=stacks_max_items,
            dry_run=bool(self.dry_run),
            serve=bool(self.serve),
            host=str(self.host).strip(),
            port=port,
            python_bin=str(self.python_bin).strip() if self.python_bin else None,
            lake_bin=str(self.lake_bin).strip() if self.lake_bin else None,
        )
        config.validate()
        return config

    def validate(self) -> None:
        if not self.repo_root.is_absolute():
            raise DeployConfigError("repo_root must be absolute")
        for name in ("repo_root", "reviewer_root", "data_root", "cache_root"):
            path = getattr(self, name)
            if not path.is_absolute():
                raise DeployConfigError(f"{name} must be absolute")
            if any(char in str(path) for char in "\x00\r\n"):
                raise DeployConfigError(f"{name} contains a control character")
        if self.stacks_root and any(
            char in str(self.stacks_root) for char in "\x00\r\n"
        ):
            raise DeployConfigError("stacks_root contains a control character")
        if self.branch and not re.fullmatch(r"v\d+\.\d+\.\d+", self.branch):
            raise DeployConfigError("branch must look like vX.Y.Z")
        if len(self.books) > 2:
            raise DeployConfigError("select at most two books per local deployment")
        if any(
            not isinstance(book, str)
            or not book.strip()
            or any(char in book for char in "\x00\r\n")
            for book in self.books
        ):
            raise DeployConfigError("books must be non-empty safe strings")
        if self.stacks_max_items < 0:
            raise DeployConfigError("stacks_max_items must not be negative")
        if not 1 <= self.port <= 65535:
            raise DeployConfigError("port must be between 1 and 65535")
        if not self.host:
            raise DeployConfigError("host must not be empty")
        if self.lake_bin and any(char in self.lake_bin for char in "\x00\r\n"):
            raise DeployConfigError("lake_bin contains a control character")
        if self.python_bin and any(char in self.python_bin for char in "\x00\r\n"):
            raise DeployConfigError("python_bin contains a control character")
        for name, path in (
            ("cache_root", self.cache_root),
            ("data_root", self.data_root),
        ):
            if (
                path == self.repo_root
                or self.repo_root in path.parents
                or path in self.repo_root.parents
            ):
                raise DeployConfigError(
                    f"{name} must be outside the ReasBook checkout: {path}"
                )
        if self.stacks_root:
            for name, path in (
                ("cache_root", self.cache_root),
                ("data_root", self.data_root),
            ):
                if (
                    path == self.stacks_root
                    or self.stacks_root in path.parents
                    or path in self.stacks_root.parents
                ):
                    raise DeployConfigError(
                        f"{name} must be outside the Stacks checkout: {path}"
                    )
        if self.data_root == self.cache_root:
            raise DeployConfigError(
                "reviewer data and cache root must be different directories"
            )
        if self.data_root in self.cache_root.parents or self.cache_root in self.data_root.parents:
            raise DeployConfigError(
                "reviewer data and cache root must not be nested"
            )

    def public_dict(self) -> dict[str, Any]:
        """Serialize configuration without environment secrets."""

        value = asdict(self)
        for key in ("repo_root", "reviewer_root", "data_root", "cache_root", "stacks_root"):
            if value[key] is not None:
                value[key] = str(value[key])
        value["books"] = list(self.books)
        return value


@dataclass(frozen=True)
class BookBuildResult:
    """Published index metadata for one book-like source project."""

    slug: str
    project: str
    branch: str
    commit: str
    target: str
    source_root: str
    index: str | None
    source_manifest: str | None
    status: str
    elapsed_seconds: float
    error: str | None = None
    cache_key: str | None = None

    def public_dict(self) -> dict[str, Any]:
        return asdict(self)


# Historical name used by the old script and downstream local tooling.
BuildResult = BookBuildResult


@dataclass(frozen=True)
class DeploymentReport:
    """Summary returned after the selected-book orchestration completes."""

    config: DeploymentConfig
    results: tuple[BookBuildResult, ...] = field(default_factory=tuple)
    manifest: Path | None = None
    stages: tuple[dict[str, Any], ...] = field(default_factory=tuple)

    def public_dict(self) -> dict[str, Any]:
        return {
            "schemaVersion": 1,
            "repo": str(self.config.repo_root),
            "cacheRoot": str(self.config.cache_root),
            "reviewerRoot": str(self.config.reviewer_root),
            "books": [result.public_dict() for result in self.results],
            "manifest": str(self.manifest) if self.manifest else None,
            "stages": list(self.stages),
        }


__all__ = [
    "BookBuildResult",
    "BuildResult",
    "DeploymentConfig",
    "DeploymentReport",
]
