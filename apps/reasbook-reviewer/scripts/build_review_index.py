#!/usr/bin/env python3
"""Build a small, deterministic review index from a Lean project directory.

This intentionally performs no Lean elaboration.  It extracts declaration
locations and file metadata so a reviewer can be brought up before the much
larger documentation and dependency-graph artifacts are available.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any

PROJECT_ROOT = Path(__file__).resolve().parents[1]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

import bootstrap  # noqa: E402,F401
from reasbook_sdk_common import atomic_write_json  # noqa: E402

DECLARATION_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|opaque|macro|syntax)\s+)*"
    r"(?P<kind>theorem|lemma|example|def|abbrev|structure|class|inductive|axiom|instance|opaque)\b"
    r"(?:\s+(?P<name>[^\s(:={]+))?"
)
COMMENT_RE = re.compile(r"^\s*--\s?(?P<text>.*)$")
STACKS_TAG_RE = re.compile(r"@\[(?P<database>stacks|kerodon)\s+(?P<tag>[0-9A-Z]{4})")


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--slug", required=True)
    parser.add_argument("--module-prefix", default="")
    parser.add_argument("--kind", default="book")
    parser.add_argument("--branch", default="")
    parser.add_argument("--commit", default="")
    parser.add_argument("--source-label", default="")
    parser.add_argument("--source-output", type=Path)
    parser.add_argument("--max-items", type=int, default=0)
    return parser.parse_args(argv)


def _safe_component(value: str) -> str:
    value = value.strip().strip("`")
    if value.startswith("«") and value.endswith("»"):
        value = value[1:-1]
    value = re.sub(r"[^A-Za-z0-9_.:-]+", "_", value)
    return value.strip("._-") or "declaration"


def _item_key(slug: str, module: str, name: str, line: int) -> str:
    module_parts = [part for part in module.split(".") if part]
    if module_parts and module_parts[0].lower() == slug.lower():
        module_parts = module_parts[1:]
    base = ".".join(part for part in ([slug, *module_parts, name]) if part)
    base = _safe_component(base.replace("/", "."))
    if len(base) <= 180:
        return base
    digest = hashlib.sha1(f"{base}:{line}".encode("utf-8")).hexdigest()[:12]
    return f"{base[:165]}_{digest}"


def _module_name(project_root: Path, source: Path, prefix: str) -> str:
    relative = source.relative_to(project_root).with_suffix("")
    components = list(relative.parts)
    if prefix:
        components.insert(0, prefix)
    return ".".join(_safe_component(component) for component in components if component)


def _doc_hint(lines: list[str], line_index: int) -> str:
    # Keep only a short, human-readable hint. Full source text remains a
    # separate optional artifact and is never embedded in the index.
    for index in range(line_index - 1, max(-1, line_index - 8), -1):
        candidate = lines[index].strip()
        if not candidate:
            continue
        if (match := COMMENT_RE.match(candidate)):
            text = match.group("text").strip()
            if text:
                return text[:240]
        if candidate.startswith("/-") or candidate.endswith("-/"):
            text = re.sub(r"^[/\-*]+|[/\-*]+$", "", candidate).strip()
            if text:
                return text[:240]
        break
    return ""


def build_index(args: argparse.Namespace) -> tuple[dict[str, Any], dict[str, Any]]:
    project_root = args.project_root.expanduser().resolve()
    if not project_root.is_dir():
        raise SystemExit(f"project root does not exist: {project_root}")

    files: list[dict[str, Any]] = []
    items: list[dict[str, Any]] = []
    seen_keys: set[str] = set()
    for source in sorted(project_root.rglob("*.lean")):
        if any(part in {".lake", ".git", "build", "_site"} for part in source.parts):
            continue
        try:
            text = source.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        lines = text.splitlines()
        relative = source.relative_to(project_root).as_posix()
        file_record = {
            "path": relative,
            "module": _module_name(project_root, source, args.module_prefix),
            "lineCount": len(lines),
            "hasSorry": bool(re.search(r"\b(?:sorry|admit)\b", text)),
        }
        files.append(file_record)
        module = str(file_record["module"])
        pending_tags: list[dict[str, str]] = []
        for line_number, line in enumerate(lines, start=1):
            if line.lstrip().startswith(("--", "/-", "*", "-/")):
                continue
            for tag_match in STACKS_TAG_RE.finditer(line):
                pending_tags.append({"database": tag_match.group("database"), "tag": tag_match.group("tag")})
            match = DECLARATION_RE.match(line)
            if not match:
                continue
            kind = match.group("kind")
            raw_name = match.group("name") or f"{kind}_{line_number}"
            name = _safe_component(raw_name)
            key = _item_key(args.slug, module, name, line_number)
            if key in seen_keys:
                digest = hashlib.sha1(f"{relative}:{line_number}".encode("utf-8")).hexdigest()[:10]
                key = f"{key[:169]}_{digest}"
            seen_keys.add(key)
            item = {
                "key": key,
                "kind": kind,
                "name": name,
                "title": _doc_hint(lines, line_number - 1) or name,
                "module": module,
                "sourcePath": relative,
                "line": line_number,
                "hasSorry": bool(re.search(r"\b(?:sorry|admit)\b", "\n".join(lines[line_number - 1 : line_number + 40]))),
            }
            if pending_tags:
                item["tags"] = pending_tags[:]
                pending_tags.clear()
            items.append(item)

    if args.max_items > 0:
        items = items[: args.max_items]
    generated_at = datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z")
    index = {
        "schemaVersion": 1,
        "state": "ready",
        "generatedAt": generated_at,
        "bookSlug": args.slug,
        "kind": args.kind,
        "branch": args.branch or None,
        "commit": args.commit or None,
        "source": args.source_label or str(project_root),
        "stats": {
            "files": len(files),
            "declarations": len(items),
            "filesWithSorry": sum(1 for entry in files if entry["hasSorry"]),
        },
        "items": items,
    }
    source_manifest = {
        "schemaVersion": 1,
        "state": "ready",
        "generatedAt": generated_at,
        "bookSlug": args.slug,
        "branch": args.branch or None,
        "commit": args.commit or None,
        "contentAvailable": False,
        "files": files,
    }
    return index, source_manifest


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    index, source_manifest = build_index(args)
    atomic_write_json(args.output.expanduser().resolve(), index)
    if args.source_output:
        atomic_write_json(args.source_output.expanduser().resolve(), source_manifest)
    print(json.dumps({"output": str(args.output), "items": len(index["items"]), "files": len(source_manifest["files"])}, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
