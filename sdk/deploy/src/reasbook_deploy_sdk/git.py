"""Git branch selection and isolated source-worktree adapters."""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
from typing import Any

from reasbook_sdk_common import Command, CommandExecutionError, CommandResult

from .errors import DeployConfigError, DeployExecutionError
from .runtime import Runner, run_command, safe_name, write_json


VERSION_BRANCH_RE = re.compile(r"^v(\d+)\.(\d+)\.(\d+)$")
PROJECT_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_-]{0,120}$")


def version_key(branch: str) -> tuple[int, int, int, str]:
    match = VERSION_BRANCH_RE.fullmatch(branch)
    if not match:
        return (-1, -1, -1, branch)
    return (int(match.group(1)), int(match.group(2)), int(match.group(3)), branch)


def project_source_rel(project: str, kind: str = "book") -> str:
    """Return the canonical entry-file path used in branch checks."""

    normalized = kind.lower()
    if normalized not in {"book", "paper"}:
        raise DeployConfigError(f"unsupported project kind: {kind!r}")
    directory = "Books" if normalized == "book" else "Papers"
    leaf = "Book.lean" if normalized == "book" else "Paper.lean"
    return f"ReasBook/{directory}/{project}/{leaf}"


class GitClient:
    """Small Git port with an injectable command runner."""

    def __init__(self, *, runner: Runner | None = None) -> None:
        self.runner = runner

    def _run(self, repo: Path, args: tuple[str, ...], *, check: bool = True) -> CommandResult:
        command = Command(("git", "-C", str(repo), *args), cwd=repo)
        try:
            result = (self.runner or _default_runner()).run(command)
        except CommandExecutionError as exc:
            raise DeployExecutionError(str(exc)) from exc
        if check and result.returncode != 0:
            detail = (result.stderr or result.stdout).strip()
            raise DeployExecutionError(
                f"git command failed: {command.display}"
                + (f"\n{detail}" if detail else "")
            )
        return result

    def output(self, repo: Path, *args: str, check: bool = True) -> str:
        return self._run(repo, tuple(args), check=check).stdout.strip()

    def run(self, repo: Path, *args: str, check: bool = True) -> CommandResult:
        """Execute a Git argv through the configured command port."""

        return self._run(repo, tuple(args), check=check)

    def branch_ref(self, repo: Path, branch: str) -> str:
        for ref in (f"origin/{branch}", branch):
            result = self._run(repo, ("rev-parse", "--verify", ref), check=False)
            if result.returncode == 0:
                return ref
        raise DeployExecutionError(f"Git ref not found: {branch}")

    def available_branches(self, repo: Path) -> list[str]:
        raw = self.output(
            repo,
            "for-each-ref",
            "--format=%(refname:short)",
            "refs/remotes/origin",
            "refs/heads",
            check=False,
        )
        branches = {
            line.removeprefix("origin/")
            for line in raw.splitlines()
            if VERSION_BRANCH_RE.fullmatch(line.removeprefix("origin/"))
        }
        return sorted(branches, key=version_key, reverse=True)

    def choose_branch(
        self,
        repo: Path,
        project: str,
        requested: str | None,
        kind: str = "book",
    ) -> str:
        path = project_source_rel(project, kind)
        if requested:
            if not VERSION_BRANCH_RE.fullmatch(requested):
                raise DeployConfigError("branch must look like vX.Y.Z")
            for ref in (f"origin/{requested}", requested):
                result = self._run(repo, ("cat-file", "-e", f"{ref}:{path}"), check=False)
                if result.returncode == 0:
                    return requested
            raise DeployExecutionError(
                f"project {project} is not present on requested branch {requested}"
            )
        for branch in self.available_branches(repo):
            ref = self.branch_ref(repo, branch)
            result = self._run(
                repo,
                ("cat-file", "-e", f"{ref}:{path}"),
                check=False,
            )
            if result.returncode == 0:
                return branch
        raise DeployExecutionError(
            f"could not find a stable version branch containing {project}"
        )

    def create_worktree(
        self,
        repo: Path,
        cache_root: Path,
        project: str,
        branch: str,
        *,
        kind: str = "book",
        dry_run: bool = False,
    ) -> Path:
        """Create or reuse a detached sparse worktree under the cache root."""

        if not PROJECT_ID_RE.fullmatch(project):
            raise DeployConfigError(f"unsafe project ID: {project!r}")
        key = f"{project}-{safe_name(branch)}"
        source_dir = cache_root / "sources" / key
        ref = self.branch_ref(repo, branch)
        desired = self.output(repo, "rev-parse", ref)
        if source_dir.is_symlink():
            raise DeployExecutionError(
                f"refusing to use symlink as a source worktree: {source_dir}"
            )
        if source_dir.exists():
            current = self.output(source_dir, "rev-parse", "HEAD", check=False)
            marker = source_dir / ".reasbook-deploy-source.json"
            marker_payload: dict[str, Any] = {}
            if marker.is_file():
                try:
                    value = json.loads(marker.read_text(encoding="utf-8"))
                    if isinstance(value, dict):
                        marker_payload = value
                except (OSError, json.JSONDecodeError):
                    pass
            marker_matches = marker_payload.get("project") == project and marker_payload.get("branch") == branch
            if current == desired and marker_matches:
                return source_dir
            if marker_matches:
                suffix = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
                source_dir = cache_root / "sources" / f"{key}-{suffix}"
            else:
                raise DeployExecutionError(
                    f"refusing to reuse non-deploy worktree: {source_dir}"
                )

        if not dry_run:
            source_dir.parent.mkdir(parents=True, exist_ok=True)
        added = False
        try:
            run_command(
                ("git", "-C", str(repo), "worktree", "add", "--detach", "--no-checkout", str(source_dir), ref),
                runner=self.runner,
                dry_run=dry_run,
            )
            added = not dry_run
            if dry_run:
                return source_dir
            sparse = run_command(
                ("git", "-C", str(source_dir), "sparse-checkout", "init", "--no-cone"),
                runner=self.runner,
                check=False,
            )
            if sparse.returncode == 0:
                patterns = (
                    "/ReasBook/*.lean",
                    "/ReasBook/lakefile.lean",
                    "/ReasBook/lean-toolchain",
                    "/ReasBook/lake-manifest.json",
                    "/ReasBook/SiteSupport/**",
                    f"/ReasBook/Books/{project}/**",
                    f"/ReasBook/Papers/{project}/**",
                )
                configured = run_command(
                    ("git", "-C", str(source_dir), "sparse-checkout", "set", "--no-cone", *patterns),
                    runner=self.runner,
                    check=False,
                )
                if configured.returncode != 0:
                    print("[deploy] warning: sparse checkout unavailable; using a full source checkout")
                    run_command(
                        ("git", "-C", str(source_dir), "sparse-checkout", "disable"),
                        runner=self.runner,
                        check=False,
                    )
            run_command(
                ("git", "-C", str(source_dir), "checkout", "--detach", ref),
                runner=self.runner,
            )
            kind_dir = "Books" if kind == "book" else "Papers"
            project_root = source_dir / "ReasBook" / kind_dir / project
            if not project_root.is_dir():
                raise DeployExecutionError(f"selected project was not checked out: {project_root}")
            write_json(
                source_dir / ".reasbook-deploy-source.json",
                {
                    "project": project,
                    "branch": branch,
                    "commit": desired,
                    "createdAt": datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z"),
                },
            )
            return source_dir
        except BaseException:
            if added:
                run_command(
                    ("git", "-C", str(repo), "worktree", "remove", "--force", str(source_dir)),
                    runner=self.runner,
                    check=False,
                )
            raise


def _default_runner() -> Runner:
    from reasbook_sdk_common import CommandRunner

    return CommandRunner(stream=False)


def working_tree_fingerprint(repo: Path, *, runner: Runner | None = None) -> tuple[str, bool]:
    """Hash tracked and untracked changes for cache provenance."""

    client = GitClient(runner=runner)
    status = client.output(repo, "status", "--porcelain=v1", "--untracked-files=all", check=False)
    diff = client.output(repo, "diff", "--binary", "HEAD", check=False)
    digest = hashlib.sha256()
    digest.update(diff.encode("utf-8", errors="replace"))
    dirty = bool(status)
    for line in status.splitlines():
        if not line.startswith("?? "):
            continue
        relative = line[3:]
        path = (repo / relative).resolve(strict=False)
        if path != repo and repo not in path.parents:
            continue
        if path.is_file() and not path.is_symlink():
            try:
                content = path.read_bytes()
            except OSError:
                continue
            digest.update(relative.encode("utf-8", errors="replace"))
            digest.update(content)
    return digest.hexdigest()[:12], dirty


__all__ = [
    "GitClient",
    "PROJECT_ID_RE",
    "VERSION_BRANCH_RE",
    "project_source_rel",
    "version_key",
    "working_tree_fingerprint",
]
