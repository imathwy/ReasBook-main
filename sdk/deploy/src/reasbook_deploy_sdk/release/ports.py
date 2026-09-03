"""Ports used by release planning and publication use cases."""

from __future__ import annotations

from typing import Protocol, Sequence

from .models import SourceProject


class ReleaseSourcePort(Protocol):
    def fetch(self) -> None:
        """Refresh moving remote refs before resolution."""

    def repository_url(self) -> str:
        """Return a credential-free source repository identifier."""

    def registry_commit(self) -> str:
        """Return the commit containing the release registry."""

    def tooling_revision(self) -> str:
        """Return a clean commit or commit plus dirty-tree fingerprint."""

    def branch_commit(self, branch: str) -> str:
        """Resolve a moving branch name to an immutable commit."""

    def read_text(self, branch: str, path: str) -> str:
        """Read one UTF-8 file from a branch without checkout."""

    def discover_projects(self, branch: str) -> Sequence[SourceProject]:
        """List buildable top-level books and papers on a branch."""


__all__ = ["ReleaseSourcePort"]
