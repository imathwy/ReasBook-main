"""Runtime locations shared by the reader, catalog tools and evidence resolver.

Generated evidence and user reviews have different lifetimes. Both live outside
the source checkout; only the review state directory needs write access at serve
time. Cache defaults follow the deployment SDK, including its environment override.
"""

import os
from pathlib import Path

import bootstrap  # noqa: F401 -- source entry points use the repository SDKs
from reasbook_deploy_sdk.runtime import default_cache_root


APP_ROOT = Path(__file__).resolve().parent
REPO_ROOT = Path(os.environ.get("REASBOOK_ROOT") or APP_ROOT.parents[1]).expanduser().resolve()


def path_setting(name: str, default: Path) -> Path:
    return Path(os.environ.get(name) or default).expanduser().resolve()


def cache_root() -> Path:
    return default_cache_root()


def data_root() -> Path:
    return path_setting("REASBOOK_REVIEWER_DATA", cache_root() / "reviewer" / "data")


def release_root() -> Path:
    return path_setting("REASBOOK_REVIEWER_RELEASE_ROOT", cache_root() / "releases")
