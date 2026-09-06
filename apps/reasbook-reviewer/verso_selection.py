"""Explicit, identity-pinned single-project Verso selection (no release mutation)."""

import hashlib
import json
from pathlib import Path
import re


def selected_verso(data_root: Path, releases: Path, *, slug: str, project_key: str,
                   branch: str, commit: str) -> tuple[Path, str] | None:
    """Return an approved producer, or retain baseline evidence on invalid input.

    The operator verifies the producer's tree digest and content before writing
    verso-selections.json atomically. Runtime checks pin that exact result and
    source identity; they never discover unapproved producers by timestamp.
    """
    try:
        manifest = json.loads((data_root / "verso-selections.json").read_text())
        if manifest.get("schemaVersion") != 1:
            return None
        entry = manifest["books"][slug]
        rid = entry["releaseId"]
        if not isinstance(rid, str) or not re.fullmatch(r"[A-Za-z0-9_-]+", rid):
            return None
        if not re.fullmatch(r"[A-Za-z0-9_.-]+", branch):
            return None
        if not re.fullmatch(r"(?:books|papers)/[A-Za-z0-9_]+", project_key):
            return None
        release = releases / rid
        root = release / "project-finalizers" / branch / project_key.replace("/", "_")
        site = root / "site"
        result_path = root / "result.json"
        if any(p.is_symlink() for p in (release, root.parent.parent, root.parent, root, site, result_path)):
            return None
        raw = result_path.read_bytes()
        if hashlib.sha256(raw).hexdigest() != entry["resultSha256"]:
            return None
        result = json.loads(raw)
        spec = json.loads((release / "release-spec.json").read_text())
        expected = {"schema_version": 1, "release_id": rid, "project_key": project_key,
                    "branch": branch, "commit": commit, "status": "success", "error": None,
                    "site_root": str(site.resolve()), "spec_digest": spec["spec_digest"]}
        if spec.get("release_id") != rid or not commit or any(result.get(k) != v for k, v in expected.items()):
            return None
        if not any(p.get("project_id") == project_key.split("/")[1]
                   and p.get("kind") == project_key.split("/")[0]
                   and p.get("branch") == branch and p.get("commit") == commit
                   for p in spec.get("projects", [])):
            return None
        stages = {s["name"]: s["status"] for s in result["stages"]}
        if stages.get("lean") != "skipped" or any(
            stages.get(name) != "success" for name in ("preflight", "verso", "stage-site")
        ):
            return None
        if not site.is_dir() or not (site / slug).is_dir():
            return None
        return site, rid
    except (OSError, ValueError, KeyError, TypeError, AttributeError):
        return None
