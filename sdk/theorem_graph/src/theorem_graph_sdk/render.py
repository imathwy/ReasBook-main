"""JSON and static-asset rendering for theorem graph pages."""

from __future__ import annotations

import html
import json
import shutil
from pathlib import Path
from typing import Any, Iterable

from reasbook_sdk_common import atomic_write_json, atomic_write_text

from .analysis import project_title
from .errors import GraphRenderError

REQUIRED_ASSETS = ("index.html", "app.js", "styles.css")


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
    except OSError as exc:
        raise GraphRenderError(f"could not copy theorem graph assets: {exc}") from exc
    _write_json(output / "data.json", data)
    items = list(data.get("items") or [])
    metadata = {
        "schemaVersion": 1,
        "project": data.get("project") or {},
        "nodes": len(items),
        "edges": sum(len(item.get("dependencies") or []) for item in items),
        "generation": data.get("generation") or {},
    }
    _write_json(output / "metadata.json", metadata)


def copy_curated_map(source: Path, output: Path) -> None:
    source = Path(source).expanduser().resolve()
    output = Path(output).expanduser().resolve()
    if not (source / "index.html").is_file():
        raise GraphRenderError(f"curated theorem map has no index.html: {source}")
    try:
        if source.is_symlink() or output.is_symlink():
            raise GraphRenderError("curated theorem map roots must not be symlinks")
        shutil.copytree(source, output, dirs_exist_ok=True, symlinks=True)
    except OSError as exc:
        raise GraphRenderError(f"could not copy curated theorem map: {exc}") from exc


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
    "REQUIRED_ASSETS",
    "collect_catalog_entries",
    "copy_curated_map",
    "copy_generic_map",
    "curated_counts",
    "read_catalog_entry",
    "write_catalog",
]
