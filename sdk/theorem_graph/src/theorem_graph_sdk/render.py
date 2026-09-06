"""JSON and static-asset rendering for theorem graph pages."""

from __future__ import annotations

import html
import json
import re
import shutil
from pathlib import Path
from typing import Any, Iterable, Mapping

from reasbook_sdk_common import atomic_write_json, atomic_write_text

from .analysis import project_title
from .errors import GraphRenderError

REQUIRED_ASSETS = ("index.html", "app.js", "styles.css")
RELEASE_CONTEXT = "release-context.json"
PROJECT_IDENTITY_FIELDS = (
    "id",
    "kind",
    "branch",
    "commit",
    "repository",
    "sourceRoot",
)


def _project_identity(value: Any) -> dict[str, Any]:
    """Return a validated, normalized release identity.

    The display branch is intentionally retained, but consumers must use the
    immutable commit when constructing source links.
    """

    if not isinstance(value, Mapping):
        raise GraphRenderError("theorem graph project identity must be an object")
    project = dict(value)
    for field in PROJECT_IDENTITY_FIELDS:
        item = project.get(field)
        if not isinstance(item, str) or not item.strip():
            raise GraphRenderError(
                f"theorem graph project identity has no valid {field}"
            )
        if any(char in item for char in "\x00\r\n"):
            raise GraphRenderError(
                f"theorem graph project identity {field} contains a control character"
            )
        project[field] = item.strip()
    project["repository"] = project["repository"].rstrip("/").removesuffix(".git")
    if not project["repository"]:
        raise GraphRenderError("theorem graph project repository is empty")
    project["sourceRoot"] = project["sourceRoot"].strip("/") + "/"
    title = project.get("title")
    if title is not None and (not isinstance(title, str) or not title.strip()):
        raise GraphRenderError("theorem graph project title must be non-empty text")
    if isinstance(title, str):
        project["title"] = title.strip()
    return project


def _release_context(project: Mapping[str, Any]) -> dict[str, Any]:
    return {"schemaVersion": 1, "project": dict(project)}


def _read_json_object(
    path: Path, *, default: dict[str, Any] | None = None
) -> dict[str, Any]:
    if not path.is_file() and default is not None:
        return dict(default)
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise GraphRenderError(f"invalid JSON object {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise GraphRenderError(f"invalid JSON object {path}: expected an object")
    return value


def _js_assignment_pattern(name: str) -> re.Pattern[str]:
    return re.compile(
        rf"^(?P<prefix>[ \t]*(?:var|let|const)[ \t]+{re.escape(name)}"
        rf"[ \t]*=[ \t]*)(?P<value>.*?)(?P<suffix>;[ \t]*)$",
        re.MULTILINE | re.DOTALL,
    )


def _replace_js_assignment(source: str, name: str, value: str) -> tuple[str, bool]:
    pattern = _js_assignment_pattern(name)

    def replacement(match: re.Match[str]) -> str:
        return (
            match.group("prefix").rstrip()
            + " "
            + json.dumps(value)
            + match.group("suffix")
        )

    updated, count = pattern.subn(replacement, source, count=1)
    return updated, count == 1


def _normalize_curated_app(output: Path, project: Mapping[str, Any]) -> None:
    """Bind the legacy curated frontend contract to this immutable release."""

    app = output / "app.js"
    if not app.is_file():
        return
    try:
        source = app.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise GraphRenderError(f"could not read curated theorem map app: {exc}") from exc
    markers = {
        name: len(tuple(_js_assignment_pattern(name).finditer(source)))
        for name in ("LEAN_REF", "LEAN_COMMIT", "LEAN_BASE")
    }
    if not any(markers.values()):
        return
    if any(count != 1 for count in markers.values()):
        invalid = ", ".join(
            f"{name}={count}" for name, count in markers.items() if count != 1
        )
        raise GraphRenderError(
            "curated theorem map uses an invalid release-link contract; "
            f"expected one assignment for each variable, got {invalid}"
        )
    source_base = (
        f'{project["repository"]}/blob/{project["commit"]}/'
        f'{project["sourceRoot"]}'
    )
    for name, value in (
        ("LEAN_REF", str(project["branch"])),
        ("LEAN_COMMIT", str(project["commit"])),
        ("LEAN_BASE", source_base),
    ):
        source, replaced = _replace_js_assignment(source, name, value)
        if not replaced:  # pragma: no cover - guarded by the marker check above
            raise GraphRenderError(f"could not normalize curated assignment {name}")
    try:
        atomic_write_text(app, source)
    except (OSError, ValueError) as exc:
        raise GraphRenderError(f"could not normalize curated theorem map app: {exc}") from exc


def _write_json(path: Path, value: Any) -> None:
    try:
        atomic_write_json(path, value)
    except (OSError, TypeError, ValueError) as exc:
        raise GraphRenderError(f"could not write JSON {path}: {exc}") from exc


def copy_generic_map(assets: Path, output: Path, data: dict[str, Any]) -> None:
    """Copy shared frontend assets and write data/metadata atomically."""

    assets = Path(assets).expanduser().resolve()
    output = Path(output).expanduser().resolve()
    missing = [name for name in REQUIRED_ASSETS if not (assets / name).is_file()]
    if missing:
        raise GraphRenderError(
            f"theorem graph assets are missing under {assets}: {', '.join(missing)}"
        )
    try:
        if assets.is_symlink() or output.is_symlink():
            raise GraphRenderError("theorem graph asset/output roots must not be symlinks")
        output.mkdir(parents=True, exist_ok=True)
        for name in REQUIRED_ASSETS:
            if (assets / name).is_symlink():
                raise GraphRenderError(f"theorem graph asset must not be a symlink: {assets / name}")
            shutil.copy2(assets / name, output / name)
        vendor = assets / "vendor"
        if vendor.is_dir():
            shutil.copytree(vendor, output / "vendor", dirs_exist_ok=True)
    except OSError as exc:
        raise GraphRenderError(f"could not copy theorem graph assets: {exc}") from exc
    rendered_data = dict(data)
    project = _project_identity(rendered_data.get("project"))
    rendered_data["project"] = project
    _write_json(output / "data.json", rendered_data)
    items = list(rendered_data.get("items") or [])
    metadata = {
        "schemaVersion": 1,
        "project": project,
        "nodes": len(items),
        "edges": sum(len(item.get("dependencies") or []) for item in items),
        "generation": rendered_data.get("generation") or {},
    }
    _write_json(output / "metadata.json", metadata)
    _write_json(output / RELEASE_CONTEXT, _release_context(project))


def copy_curated_map(
    source: Path,
    output: Path,
    *,
    project: Mapping[str, Any],
) -> None:
    """Copy a curated map and bind it to the current release identity."""

    source_input = Path(source).expanduser()
    output_input = Path(output).expanduser()
    if source_input.is_symlink() or output_input.is_symlink():
        raise GraphRenderError("curated theorem map roots must not be symlinks")
    source = source_input.resolve()
    output = output_input.resolve()
    if not (source / "index.html").is_file():
        raise GraphRenderError(f"curated theorem map has no index.html: {source}")
    for path in source.rglob("*"):
        if path.is_symlink():
            raise GraphRenderError(f"curated theorem map must not contain symlinks: {path}")
    identity = _project_identity(project)
    nodes, edges = curated_counts(source)
    try:
        shutil.copytree(source, output, dirs_exist_ok=True)
    except OSError as exc:
        raise GraphRenderError(f"could not copy curated theorem map: {exc}") from exc
    metadata = _read_json_object(
        output / "metadata.json",
        default={
            "schemaVersion": 1,
            "nodes": nodes,
            "edges": edges,
            "generation": {"mode": "curated-static"},
        },
    )
    metadata["schemaVersion"] = 1
    metadata["project"] = identity
    metadata["nodes"] = nodes
    metadata["edges"] = edges
    metadata.setdefault("generation", {"mode": "curated-static"})
    _write_json(output / "metadata.json", metadata)
    _write_json(output / RELEASE_CONTEXT, _release_context(identity))
    _normalize_curated_app(output, identity)


def curated_counts(source: Path) -> tuple[int, int]:
    """Read counts from metadata, falling back to data.json when needed."""

    source = Path(source)
    metadata_path = source / "metadata.json"
    data_path = source / "data.json"
    try:
        if metadata_path.is_file():
            metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
            return int(metadata.get("nodes") or 0), int(metadata.get("edges") or 0)
        if data_path.is_file():
            data = json.loads(data_path.read_text(encoding="utf-8"))
            items = list(data.get("items") or [])
            return len(items), sum(
                len(item.get("dependencies") or []) for item in items
            )
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        raise GraphRenderError(
            f"invalid theorem map metadata under {source}: {exc}"
        ) from exc
    return 0, 0


def read_catalog_entry(map_root: Path, kind: str) -> dict[str, Any]:
    metadata_path = map_root / "metadata.json"
    data_path = map_root / "data.json"
    try:
        if metadata_path.is_file():
            metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
        elif data_path.is_file():
            data = json.loads(data_path.read_text(encoding="utf-8"))
            items = list(data.get("items") or [])
            metadata = {
                "project": data.get("project") or {},
                "nodes": len(items),
                "edges": sum(len(item.get("dependencies") or []) for item in items),
            }
        else:
            metadata = {}
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        raise GraphRenderError(f"invalid metadata under {map_root}: {exc}") from exc
    if not isinstance(metadata, dict):
        raise GraphRenderError(f"invalid metadata under {map_root}: expected an object")
    project = metadata.get("project") or {}
    if not isinstance(project, dict):
        raise GraphRenderError(
            f"invalid metadata under {map_root}: project must be an object"
        )
    try:
        nodes = max(0, int(metadata.get("nodes") or 0))
        edges = max(0, int(metadata.get("edges") or 0))
    except (TypeError, ValueError) as exc:
        raise GraphRenderError(
            f"invalid metadata under {map_root}: counts must be integers"
        ) from exc
    return {
        "title": project.get("title") or map_root.name.replace("_", " "),
        "id": project.get("id") or map_root.name,
        "kind": kind,
        "slug": map_root.name,
        "branch": project.get("branch") or "",
        "nodes": nodes,
        "edges": edges,
    }


def collect_catalog_entries(site_root: Path) -> list[dict[str, Any]]:
    maps_root = Path(site_root) / "theorem-maps"
    entries: list[dict[str, Any]] = []
    for kind in ("books", "papers"):
        kind_root = maps_root / kind
        if not kind_root.is_dir():
            continue
        for map_root in sorted(kind_root.iterdir(), key=lambda path: path.name.lower()):
            if map_root.is_dir() and (map_root / "index.html").is_file():
                entries.append(read_catalog_entry(map_root, kind))
    return sorted(entries, key=lambda item: (item["kind"], item["title"].lower()))


def _normalize_catalog_entry(entry: Any) -> dict[str, Any]:
    """Accept current dictionaries and the legacy tuple form."""

    if isinstance(entry, tuple) and len(entry) == 3:
        project, nodes, edges = entry
        return {
            "id": project.project_id,
            "title": project_title(project),
            "kind": project.kind,
            "slug": project.slug,
            "branch": "",
            "nodes": nodes,
            "edges": edges,
        }
    return dict(entry)


def write_catalog(
    site_root: Path,
    entries: Iterable[dict[str, Any]] | None = None,
    *,
    include_branch: bool = True,
) -> Path:
    """Write the cross-project catalog and return its path."""

    site_root = Path(site_root).expanduser().resolve()
    entries = (
        [_normalize_catalog_entry(entry) for entry in entries]
        if entries is not None
        else collect_catalog_entries(site_root)
    )
    rows = []
    for entry in entries:
        try:
            nodes = max(0, int(entry.get("nodes") or 0))
            edges = max(0, int(entry.get("edges") or 0))
        except (AttributeError, TypeError, ValueError) as exc:
            raise GraphRenderError("catalog entries must contain integer node/edge counts") from exc
        href = f'./{entry["kind"]}/{entry["slug"]}/'
        branch_cell = (
            f'<td><code>{html.escape(str(entry["branch"]))}</code></td>'
            if include_branch
            else ""
        )
        rows.append(
            "      <tr>"
            f'<td><a href="{html.escape(href, quote=True)}">{html.escape(str(entry["title"]))}</a></td>'
            f'<td>{html.escape(str(entry["kind"])[:-1].title())}</td>'
            f"{branch_cell}"
            f'<td>{nodes}</td><td>{edges}</td>'
            "</tr>"
        )
    if include_branch:
        headers = (
            "    <thead><tr><th>Project</th><th>Kind</th><th>Branch</th>"
            "<th>Nodes</th><th>Edges</th></tr></thead>"
        )
    else:
        headers = (
            "    <thead><tr><th>Project</th><th>Kind</th>"
            "<th>Nodes</th><th>Edges</th></tr></thead>"
        )
    catalog = site_root / "theorem-maps" / "index.html"
    content = "\n".join(
        [
            "<!doctype html>",
            '<html lang="en">',
            "<head>",
            '  <meta charset="utf-8">',
            '  <meta name="viewport" content="width=device-width,initial-scale=1">',
            "  <title>ReasBook Theorem Maps</title>",
            "  <style>",
            "    :root{color-scheme:light}body{font:16px/1.5 system-ui,sans-serif;max-width:1120px;margin:40px auto;padding:0 20px;color:#1d2833;background:#f7f9fb}",
            "    h1{letter-spacing:0}p{color:#526170}table{width:100%;border-collapse:collapse;background:#fff;border:1px solid #d8dee5}",
            "    th,td{padding:10px 12px;border-bottom:1px solid #d8dee5;text-align:left}a{color:#245aa8}th{font-size:13px;text-transform:uppercase;color:#586675;letter-spacing:0}",
            "    @media(max-width:720px){body{margin:20px auto}th:nth-child(3),td:nth-child(3){display:none}th,td{padding:8px}}",
            "  </style>",
            "</head>",
            "<body>",
            "  <h1>ReasBook Theorem Maps</h1>",
            "  <p>Natural-language statements, literature-level declarations, and their Lean dependencies.</p>",
            "  <table>",
            headers,
            "    <tbody>",
            *rows,
            "    </tbody>",
            "  </table>",
            '  <p><a href="../">Back to ReasBook</a></p>',
            "</body>",
            "</html>",
            "",
        ]
    )
    try:
        catalog.parent.mkdir(parents=True, exist_ok=True)
        atomic_write_text(catalog, content)
    except (OSError, ValueError) as exc:
        raise GraphRenderError(f"could not write theorem map catalog: {exc}") from exc
    return catalog


__all__ = [
    "PROJECT_IDENTITY_FIELDS",
    "REQUIRED_ASSETS",
    "RELEASE_CONTEXT",
    "collect_catalog_entries",
    "copy_curated_map",
    "copy_generic_map",
    "curated_counts",
    "read_catalog_entry",
    "write_catalog",
]
