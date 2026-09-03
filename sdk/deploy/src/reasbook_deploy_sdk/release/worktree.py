"""Detached Git worktrees used by one immutable release."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Mapping

from reasbook_sdk_common import atomic_write_json

from ..errors import DeployExecutionError
from ..git import GitClient
from ..runtime import safe_name
from .models import BranchSpec, ReleaseSpec
from .store import ReleaseLayout


class ReleaseWorktreeManager:
    """Create and validate detached release worktrees sequentially."""

    def __init__(
        self,
        repo_root: Path,
        layout: ReleaseLayout,
        *,
        git: GitClient | None = None,
    ) -> None:
        self.repo_root = Path(repo_root).expanduser().resolve()
        self.layout = layout
        self.git = git or GitClient()

    def prepare(self, spec: ReleaseSpec, branch: BranchSpec) -> Path:
        worktree = self.layout.worktrees / safe_name(branch.name)
        marker = worktree / ".reasbook-release-source.json"
        if worktree.is_symlink():
            raise DeployExecutionError(f"release worktree is a symlink: {worktree}")
        if worktree.exists():
            self._validate_existing(spec, branch, worktree, marker)
            return worktree
        worktree.parent.mkdir(parents=True, exist_ok=True)
        result = self.git.run(
            self.repo_root,
            "worktree",
            "add",
            "--detach",
            str(worktree),
            branch.commit,
            check=False,
        )
        if result.returncode != 0:
            detail = (result.stderr or result.stdout).strip()
            raise DeployExecutionError(
                f"could not create release worktree for {branch.name}"
                + (f": {detail}" if detail else "")
            )
        try:
            atomic_write_json(marker, self._marker(spec, branch))
        except BaseException:
            self.git.run(
                self.repo_root,
                "worktree",
                "remove",
                "--force",
                str(worktree),
                check=False,
            )
            raise
        return worktree

    @staticmethod
    def _marker(spec: ReleaseSpec, branch: BranchSpec) -> dict[str, str | int]:
        return {
            "schema_version": 1,
            "release_id": spec.release_id,
            "spec_digest": spec.spec_digest,
            "branch": branch.name,
            "commit": branch.commit,
        }

    def _validate_existing(
        self,
        spec: ReleaseSpec,
        branch: BranchSpec,
        worktree: Path,
        marker: Path,
    ) -> None:
        try:
            value = json.loads(marker.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise DeployExecutionError(
                f"release worktree marker is invalid: {marker}"
            ) from exc
        expected = self._marker(spec, branch)
        if not isinstance(value, Mapping) or any(
            value.get(key) != item for key, item in expected.items()
        ):
            raise DeployExecutionError(
                f"release worktree belongs to another plan: {worktree}"
            )
        actual = self.git.output(worktree, "rev-parse", "HEAD", check=False)
        if actual != branch.commit:
            raise DeployExecutionError(f"release worktree commit mismatch: {worktree}")


__all__ = ["ReleaseWorktreeManager"]
