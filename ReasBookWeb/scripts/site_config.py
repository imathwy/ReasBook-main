"""Environment-derived settings for the ReasBook web generator.

The generator writes a number of different artifacts, but all of them need the
same repository identity, branch and URL rules.  Keeping those rules here
leaves ``gen_sections.py`` focused on discovering entries and rendering pages.
"""

from __future__ import annotations

from dataclasses import dataclass
import os
import re
import subprocess


def _git_output(args: list[str]) -> str:
    try:
        return subprocess.check_output(args, text=True, stderr=subprocess.DEVNULL).strip()
    except (OSError, subprocess.SubprocessError):
        return ""


def _git_config_get(key: str) -> str:
    return _git_output(["git", "config", "--get", key])


def _current_git_branch() -> str:
    return _git_output(["git", "branch", "--show-current"])


def parse_github_remote(url: str) -> tuple[str, str] | None:
    """Parse HTTPS and SSH GitHub remote forms into ``(owner, repo)``."""

    value = (url or "").strip()
    if not value:
        return None
    patterns = (
        r"^https?://github\.com/([^/]+)/([^/]+?)(?:\.git)?/?$",
        r"^git@github\.com:([^/]+)/([^/]+?)(?:\.git)?/?$",
    )
    for pattern in patterns:
        match = re.match(pattern, value)
        if match:
            return match.group(1), match.group(2)
    return None


def parse_repo_slug(slug: str) -> tuple[str, str] | None:
    value = (slug or "").strip().strip("/")
    parts = value.split("/") if value else []
    if len(parts) != 2:
        return None
    owner, repo = (part.strip() for part in parts)
    return (owner, repo) if owner and repo else None


def _remote_url(name: str) -> str:
    return _git_config_get(f"remote.{name}.url") if name else ""


def _candidate_remotes() -> list[str]:
    names: list[str] = []
    configured = os.environ.get("REASBOOK_GIT_REMOTE_NAME", "").strip()
    if configured:
        names.append(configured)

    branch = _current_git_branch()
    if branch:
        branch_remote = _git_config_get(f"branch.{branch}.remote")
        if branch_remote:
            names.append(branch_remote)

    push_default = _git_config_get("remote.pushDefault")
    if push_default:
        names.append(push_default)
    names.extend(("origin", "upstream"))

    result: list[str] = []
    seen: set[str] = set()
    for name in names:
        if name and name not in seen:
            seen.add(name)
            result.append(name)
    return result


def detect_default_branch() -> str:
    for remote in _candidate_remotes():
        ref = _git_output(["git", "symbolic-ref", "--quiet", "--short", f"refs/remotes/{remote}/HEAD"])
        prefix = f"{remote}/"
        if ref.startswith(prefix) and ref[len(prefix) :].strip():
            return ref[len(prefix) :].strip()
    return ""


def detect_github_repo() -> tuple[str, str]:
    for key in ("REASBOOK_GITHUB_REPO", "GITHUB_REPOSITORY"):
        parsed = parse_repo_slug(os.environ.get(key, ""))
        if parsed is not None:
            return parsed

    urls = []
    configured_url = os.environ.get("REASBOOK_GIT_REMOTE_URL", "").strip()
    if configured_url:
        urls.append(configured_url)
    urls.extend(filter(None, (_remote_url(name) for name in _candidate_remotes())))
    for url in urls:
        parsed = parse_github_remote(url)
        if parsed is not None:
            return parsed
    return "optsuite", "ReasBook"


def parse_csv_env_set(name: str) -> set[str]:
    raw = os.environ.get(name, "").strip()
    return {item.strip() for item in raw.split(",") if item.strip()}


DEFAULT_SKIP_MODULES = {
    "Books.ConvexAnalysis_Rockafellar_1970.Chap02.section09_part12",
}
SKIP_MODULES = DEFAULT_SKIP_MODULES | parse_csv_env_set("REASBOOK_SKIP_MODULES")
INCLUDE_PROJECTS = parse_csv_env_set("REASBOOK_INCLUDE_PROJECTS")
EXCLUDE_PROJECTS = parse_csv_env_set("REASBOOK_EXCLUDE_PROJECTS")


def project_enabled(kind: str, project: str) -> bool:
    """Apply optional release-level project selection."""

    key = f"{kind.strip().lower()}/{project}"
    if key in EXCLUDE_PROJECTS:
        return False
    return not INCLUDE_PROJECTS or key in INCLUDE_PROJECTS


@dataclass(frozen=True)
class SiteConfig:
    github_owner: str
    github_repo: str
    github_branch: str
    site_base: str
    site_root: str
    docs_base: str


def load_site_config() -> SiteConfig:
    owner, repo = detect_github_repo()
    branch = (
        os.environ.get("REASBOOK_GITHUB_BRANCH", "").strip()
        or os.environ.get("GITHUB_REF_NAME", "").strip()
        or detect_default_branch()
        or _current_git_branch()
        or "main"
    )
    site_base = (
        os.environ.get("REASBOOK_SITE_BASE")
        or f"https://{owner}.github.io/{repo}/"
    ).rstrip("/") + "/"
    default_root = "/" if repo == f"{owner}.github.io" else f"/{repo}/"
    site_root = (os.environ.get("REASBOOK_SITE_ROOT") or default_root).strip()
    if not site_root.startswith("/"):
        site_root = f"/{site_root}"
    if not site_root.endswith("/"):
        site_root = f"{site_root}/"
    return SiteConfig(
        github_owner=owner,
        github_repo=repo,
        github_branch=branch,
        site_base=site_base,
        site_root=site_root,
        docs_base=f"{site_base}docs/ReasBook/",
    )
