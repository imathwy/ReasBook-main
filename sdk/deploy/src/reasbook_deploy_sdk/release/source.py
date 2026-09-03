"""Git adapter for resolving immutable release inputs."""

from __future__ import annotations

from pathlib import Path
import re
from urllib.parse import urlsplit, urlunsplit

from ..errors import DeployExecutionError
from ..git import GitClient, working_tree_fingerprint
from .models import SourceProject
from .tooling import bind_tooling_revision, tooling_source_digest


def _credential_free_remote(value: str) -> str:
    remote = value.strip()
    if not remote:
        return ""
    if remote.startswith("git@github.com:"):
        path = remote.removeprefix("git@github.com:").removesuffix(".git")
        return f"https://github.com/{path}.git"
    if "://" not in remote:
        return remote
    parsed = urlsplit(remote)
    hostname = parsed.hostname or ""
    if parsed.port:
        hostname = f"{hostname}:{parsed.port}"
    return urlunsplit((parsed.scheme, hostname, parsed.path, "", ""))


class GitReleaseSource:
    """Read branch snapshots directly from Git objects."""

    def __init__(self, repo_root: Path, *, git: GitClient | None = None) -> None:
        self.repo_root = Path(repo_root).expanduser().resolve()
        self.git = git or GitClient()
        self._refs: dict[str, str] = {}

    def _ref(self, branch: str) -> str:
        if branch not in self._refs:
            self._refs[branch] = self.git.branch_ref(self.repo_root, branch)
        return self._refs[branch]

    def fetch(self) -> None:
        self.git.run(
            self.repo_root,
            "fetch",
            "--prune",
            "origin",
        )
        self._refs.clear()

    def repository_url(self) -> str:
        remote = self.git.output(
            self.repo_root, "remote", "get-url", "origin", check=False
        )
        return _credential_free_remote(remote) or "local"

    def registry_commit(self) -> str:
        return self.git.output(self.repo_root, "rev-parse", "HEAD")

    def tooling_revision(self) -> str:
        commit = self.registry_commit()
        fingerprint, dirty = working_tree_fingerprint(self.repo_root)
        revision = f"{commit}+dirty:{fingerprint}" if dirty else commit
        return bind_tooling_revision(
            revision,
            tooling_source_digest(self.repo_root),
        )

    def branch_commit(self, branch: str) -> str:
        return self.git.output(self.repo_root, "rev-parse", self._ref(branch))

    def read_text(self, branch: str, path: str) -> str:
        if (
            not path
            or path.startswith("/")
            or ".." in Path(path).parts
            or any(char in path for char in "\x00\r\n")
        ):
            raise DeployExecutionError(f"unsafe Git object path: {path!r}")
        return self.git.run(
            self.repo_root,
            "show",
            f"{self._ref(branch)}:{path}",
        ).stdout

    def discover_projects(self, branch: str) -> tuple[SourceProject, ...]:
        raw = self.git.output(
            self.repo_root,
            "ls-tree",
            "-r",
            "--name-only",
            self._ref(branch),
            "ReasBook/Books",
            "ReasBook/Papers",
            check=False,
        )
        projects: set[tuple[str, str]] = set()
        pattern = re.compile(
            r"^ReasBook/(?P<kind>Books|Papers)/"
            r"(?P<project>[A-Za-z0-9][A-Za-z0-9_.-]*)/"
            r"(?P<leaf>Book|Paper)\.lean$"
        )
        for line in raw.splitlines():
            match = pattern.fullmatch(line)
            if not match:
                continue
            kind = "books" if match.group("kind") == "Books" else "papers"
            expected = "Book" if kind == "books" else "Paper"
            if match.group("leaf") == expected:
                projects.add((kind, match.group("project")))
        return tuple(SourceProject(kind, project) for kind, project in sorted(projects))


__all__ = ["GitReleaseSource"]
