"""Shared, argv-only access to a trusted GitHub repository checkout."""

from __future__ import annotations

import json
import math
from pathlib import Path
import re
import time
from typing import Any
from urllib.parse import quote

from reasbook_sdk_common import Command, CommandExecutionError, CommandRunner

from ..errors import DeployExecutionError
from .models import GitHubPublishProfile


GITHUB_API_VERSION = "2026-03-10"
GITHUB_JSON_ACCEPT = "application/vnd.github+json"


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
            raise DeployExecutionError(
                "GitHub returned an invalid default-branch commit"
            )
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

    def _immutable_releases_enabled(self) -> bool:
        """Return the repository setting without treating API failure as disabled."""

        endpoint = f"repos/{self.profile.repository}/immutable-releases"
        result = self._run(
            "api",
            endpoint,
            "--method",
            "GET",
            "-H",
            f"Accept: {GITHUB_JSON_ACCEPT}",
            "-H",
            f"X-GitHub-Api-Version: {GITHUB_API_VERSION}",
            check=False,
        )
        if result.returncode != 0:
            detail = (result.stderr or result.stdout).strip()
            status = self._http_status(detail)
            if status == 404:
                # GitHub documents 404 as the disabled response for this
                # endpoint. Current GitHub.com also returns 200/false, which is
                # handled below.
                return False
            if status in {401, 403}:
                raise DeployExecutionError(
                    "cannot inspect GitHub immutable releases: the token needs "
                    "repository Administration (read) permission"
                )
            raise DeployExecutionError(
                "cannot inspect GitHub immutable releases"
                + (f": {detail}" if detail else "")
            )
        try:
            value = json.loads(result.stdout)
        except json.JSONDecodeError as exc:
            raise DeployExecutionError(
                "GitHub returned invalid immutable-releases JSON"
            ) from exc
        if (
            not isinstance(value, dict)
            or not isinstance(value.get("enabled"), bool)
            or not isinstance(value.get("enforced_by_owner"), bool)
        ):
            raise DeployExecutionError(
                "GitHub immutable-releases response is incomplete"
            )
        return value["enabled"]

    def _require_immutable_releases_enabled(self) -> None:
        if not self._immutable_releases_enabled():
            raise DeployExecutionError(
                "GitHub immutable releases are disabled; run `release "
                "configure-pages --profile github-pages` with an admin token"
            )

    def _wait_for_immutable_releases_enabled(
        self,
        *,
        timeout_seconds: float,
        poll_interval_seconds: float,
    ) -> None:
        """Wait for GitHub's repository setting to reflect a successful write."""

        deadline = time.monotonic() + timeout_seconds
        while True:
            if self._immutable_releases_enabled():
                return
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise DeployExecutionError(
                    "timed out waiting for GitHub immutable releases to become "
                    "enabled"
                )
            time.sleep(min(poll_interval_seconds, remaining))

    def _enable_immutable_releases(self) -> None:
        endpoint = f"repos/{self.profile.repository}/immutable-releases"
        result = self._run(
            "api",
            endpoint,
            "--method",
            "PUT",
            "-H",
            f"Accept: {GITHUB_JSON_ACCEPT}",
            "-H",
            f"X-GitHub-Api-Version: {GITHUB_API_VERSION}",
            check=False,
        )
        if result.returncode == 0:
            return
        detail = (result.stderr or result.stdout).strip()
        status = self._http_status(detail)
        if status in {401, 403}:
            raise DeployExecutionError(
                "cannot enable GitHub immutable releases: the token needs "
                "repository Administration (write) permission"
            )
        if status == 409:
            raise DeployExecutionError(
                "cannot enable GitHub immutable releases: GitHub reported a conflict"
            )
        raise DeployExecutionError(
            "cannot enable GitHub immutable releases"
            + (f": {detail}" if detail else "")
        )

    @staticmethod
    def _http_status(detail: str) -> int | None:
        for pattern in (
            r"\bHTTP(?:/\d(?:\.\d)?)?\s+([1-5]\d\d)\b",
            r"\b([1-5]\d\d)\s+(?:Unauthorized|Forbidden|Not Found|Conflict)\b",
        ):
            match = re.search(pattern, detail, re.I)
            if match:
                return int(match.group(1))
        return None

    def _run(
        self,
        *args: str,
        check: bool = True,
        input_value: dict[str, Any] | None = None,
        timeout_seconds: float = 300.0,
    ):
        if not math.isfinite(timeout_seconds) or timeout_seconds <= 0:
            raise DeployExecutionError("GitHub command timeout must be positive")
        try:
            result = self.runner.run(
                Command(
                    ("gh", *args),
                    cwd=self.repo_root,
                    timeout=timeout_seconds,
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
            raise DeployExecutionError(
                f"cannot inspect local Git state: {exc}"
            ) from exc
        if result.returncode != 0:
            detail = (result.stderr or result.stdout).strip()
            raise DeployExecutionError(
                "local Git inspection failed" + (f": {detail}" if detail else "")
            )
        return result


__all__ = [
    "GITHUB_API_VERSION",
    "GITHUB_JSON_ACCEPT",
    "GitHubRepositoryClient",
]
