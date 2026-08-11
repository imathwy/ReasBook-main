#!/usr/bin/env python3
"""Rebuild the theorem-map catalog after version-branch site artifacts merge."""

from __future__ import annotations

import argparse
import html
import json
from pathlib import Path
from typing import Any


def read_entry(map_root: Path, kind: str) -> dict[str, Any]:
    metadata_path = map_root / "metadata.json"
    data_path = map_root / "data.json"
    if metadata_path.is_file():
        metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    elif data_path.is_file():
        data = json.loads(data_path.read_text(encoding="utf-8"))
        items = list(data.get("items") or [])
        metadata = {
            "project": data.get("project") or {},
            "nodes": len(items),
            "edges": sum(
                len(item.get("dependencies") or []) for item in items
            ),
        }
    else:
        metadata = {}
    project = metadata.get("project") or {}
    return {
        "title": project.get("title") or map_root.name.replace("_", " "),
        "id": project.get("id") or map_root.name,
        "kind": kind,
        "slug": map_root.name,
        "branch": project.get("branch") or "",
        "nodes": int(metadata.get("nodes") or 0),
        "edges": int(metadata.get("edges") or 0),
    }


def collect_entries(site_root: Path) -> list[dict[str, Any]]:
    entries = []
    maps_root = site_root / "theorem-maps"
    for kind in ("books", "papers"):
        kind_root = maps_root / kind
        if not kind_root.is_dir():
            continue
        for map_root in sorted(kind_root.iterdir()):
            if map_root.is_dir() and (map_root / "index.html").is_file():
                entries.append(read_entry(map_root, kind))
    return sorted(entries, key=lambda item: (item["kind"], item["title"].lower()))


def write_catalog(site_root: Path) -> Path:
    entries = collect_entries(site_root)
    rows = []
    for entry in entries:
        href = f'./{entry["kind"]}/{entry["slug"]}/'
        rows.append(
            "      <tr>"
            f'<td><a href="{html.escape(href)}">{html.escape(entry["title"])}</a></td>'
            f'<td>{html.escape(entry["kind"][:-1].title())}</td>'
            f'<td><code>{html.escape(entry["branch"])}</code></td>'
            f'<td>{entry["nodes"]}</td><td>{entry["edges"]}</td>'
            "</tr>"
        )
    catalog = site_root / "theorem-maps" / "index.html"
    catalog.parent.mkdir(parents=True, exist_ok=True)
    catalog.write_text(
        "\n".join(
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
                "    <thead><tr><th>Project</th><th>Kind</th><th>Branch</th><th>Nodes</th><th>Edges</th></tr></thead>",
                "    <tbody>",
                *rows,
                "    </tbody>",
                "  </table>",
                '  <p><a href="../">Back to ReasBook</a></p>',
                "</body>",
                "</html>",
                "",
            ]
        ),
        encoding="utf-8",
    )
    return catalog


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--site-root", type=Path, default=Path("ReasBookWeb/_site"))
    args = parser.parse_args()
    catalog = write_catalog(args.site_root.resolve())
    print(f"[theorem-map] wrote merged catalog: {catalog}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
