"""Shared, argv-only access to a trusted GitHub repository checkout."""

from __future__ import annotations

import json
from pathlib import Path
import re
from typing import Any
from urllib.parse import quote

from reasbook_sdk_common import Command, CommandExecutionError, CommandRunner

from ..errors import DeployExecutionError
from .models import GitHubPublishProfile


class GitHubRepositoryClient:
    """GitHub CLI adapter with a clean default-branch checkout boundary."""

    def __init__(
        self,
        profile: GitHubPublishProfile,
        *,
        runner: CommandRunner | None = None,
        repo_root: Path | None = None,
    ) -> None:
        self.profile = profile
        self.runner = runner or CommandRunner()
        self.repo_root = Path(repo_root or Path.cwd()).expanduser().resolve()

    def _default_branch(self) -> str:
        result = self._run(
            "repo",
            "view",
            self.profile.repository,
            "--json",
            "defaultBranchRef",
            "--jq",
            ".defaultBranchRef.name",
        )
        ref = result.stdout.strip()
        if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._/-]*", ref) or ".." in ref:
            raise DeployExecutionError("GitHub returned an unsafe default branch")
        return ref

    def _trusted_target(self, ref: str | None = None) -> str:
        default_branch = ref or self._default_branch()
        target = self._run(
            "api",
            f"repos/{self.profile.repository}/commits/{quote(default_branch, safe='')}",
            "--jq",
            ".sha",
        ).stdout.strip()
        if not re.fullmatch(r"[0-9a-f]{40}", target):
            raise DeployExecutionError("GitHub returned an invalid default-branch commit")
        local_head = self._git("rev-parse", "HEAD").stdout.strip()
        if local_head != target:
            raise DeployExecutionError(
                "local HEAD is not the GitHub default-branch commit; merge and "
                "pull the release tooling before publishing"
            )
        dirty = self._git(
            "status",
            "--porcelain=v1",
            "--untracked-files=all",
        ).stdout.strip()
        if dirty:
            raise DeployExecutionError(
                "release publication requires a clean Git working tree"
            )
        return target

    def _run(
        self,
        *args: str,
        check: bool = True,
        input_value: dict[str, Any] | None = None,
    ):
        try:
            result = self.runner.run(
                Command(
                    ("gh", *args),
                    cwd=self.repo_root,
                    timeout=300.0,
                    input_text=(
                        json.dumps(input_value, separators=(",", ":"))
                        if input_value is not None
                        else None
                    ),
                )
            )
        except CommandExecutionError as exc:
            raise DeployExecutionError(f"cannot run GitHub CLI: {exc}") from exc
        if check and result.returncode != 0:
            detail = (result.stderr or result.stdout).strip()
            raise DeployExecutionError(
                f"GitHub CLI command failed: {' '.join(args[:2])}"
                + (f": {detail}" if detail else "")
            )
        return result

    def _git(self, *args: str):
        try:
            result = self.runner.run(
                Command(("git", *args), cwd=self.repo_root, timeout=60.0)
            )
        except CommandExecutionError as exc:
            raise DeployExecutionError(f"cannot inspect local Git state: {exc}") from exc
        if result.returncode != 0:
            detail = (result.stderr or result.stdout).strip()
            raise DeployExecutionError(
                "local Git inspection failed" + (f": {detail}" if detail else "")
            )
        return result


__all__ = ["GitHubRepositoryClient"]
