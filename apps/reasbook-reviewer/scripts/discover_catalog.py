#!/usr/bin/env python3
"""Generate the lightweight ReasBook reviewer catalog.

This command deliberately does not invoke Lake, Lean, doc-gen, or dependency
extractors.  It is safe to run while the full per-book build pipeline is still
being designed.
"""

from __future__ import annotations

import argparse
from dataclasses import replace
from datetime import datetime, timezone
import json
from pathlib import Path
import sys

PROJECT_ROOT = Path(__file__).resolve().parents[1]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

import bootstrap  # noqa: E402,F401
from settings import data_root  # noqa: E402
from catalog import (  # noqa: E402
    catalog_payload,
    default_reasbook_root,
    discover_books,
    discover_stacks_project,
    write_catalog,
)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reasbook-root", type=Path, default=default_reasbook_root())
    parser.add_argument("--output", type=Path, default=data_root() / "catalog.json")
    parser.add_argument("--include-papers", action="store_true", help="also list ReasBook/Papers projects")
    parser.add_argument("--include-stacks", action="store_true", help="include the sibling Stacks Lean project")
    parser.add_argument("--stacks-root", type=Path, help="Stacks project checkout (used with --include-stacks)")
    parser.add_argument("--data-root", type=Path, default=data_root(), help="reviewer data root used to mark existing indexes ready")
    parser.add_argument("--stamp", action="store_true", help="write the current UTC time as generatedAt")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv or sys.argv[1:])
    records = discover_books(args.reasbook_root, include_papers=args.include_papers)
    extra_sources: list[dict[str, object]] = []
    if args.include_stacks:
        stacks = discover_stacks_project(args.stacks_root)
        if stacks is not None:
            records.append(stacks)
            extra_sources.append({"repository": "Review", "root": stacks.source_root})

    # Preserve the small catalog format while reflecting indexes already built
    # by the selected-book deploy command.
    if args.data_root:
        data_root = args.data_root.expanduser().resolve()
        hydrated = []
        for record in records:
            index_path = data_root / "books" / record.slug / "index.json"
            state = record.review_index_state
            item_count = record.item_count
            try:
                payload = json.loads(index_path.read_text(encoding="utf-8"))
                if isinstance(payload, dict) and isinstance(payload.get("items"), list):
                    state = str(payload.get("state") or "ready")
                    item_count = len(payload["items"])
            except (OSError, ValueError, TypeError):
                pass
            updated = replace(record, review_index_state=state, item_count=item_count)
            # ``BookRecord`` keeps the compact schema; artifact readiness is
            # derived by the API and by this generated catalog from files that
            # actually exist under the data root.
            hydrated.append(updated)
        records = hydrated

    payload = catalog_payload(records, reasbook_root=args.reasbook_root, extra_sources=extra_sources)
    if args.data_root:
        data_root = args.data_root.expanduser().resolve()
        for entry in payload["books"]:
            slug = entry.get("slug")
            if not isinstance(slug, str):
                continue
            artifacts = entry.get("artifacts") if isinstance(entry.get("artifacts"), dict) else {}
            for name in ("index", "source", "docs", "graphs"):
                artifact_path = data_root / "books" / slug / f"{name}.json"
                spec = artifacts.get(name) if isinstance(artifacts.get(name), dict) else {}
                if artifact_path.is_file():
                    spec["state"] = "ready"
                    if name == "source":
                        try:
                            source_payload = json.loads(artifact_path.read_text(encoding="utf-8"))
                            if isinstance(source_payload, dict) and source_payload.get("contentAvailable") is False:
                                spec["state"] = "partial"
                        except (OSError, ValueError, TypeError):
                            pass
                    try:
                        spec["sizeBytes"] = artifact_path.stat().st_size
                    except OSError:
                        pass
                artifacts[name] = spec
            entry["artifacts"] = artifacts
            review_index = entry.get("reviewIndex") if isinstance(entry.get("reviewIndex"), dict) else {}
            review_index["state"] = artifacts.get("index", {}).get("state", review_index.get("state", "not-built"))
            review_index["itemCount"] = next(
                (record.item_count for record in records if record.slug == slug),
                review_index.get("itemCount", 0),
            )
            entry["reviewIndex"] = review_index
    if args.stamp:
        payload["generatedAt"] = datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z")
    write_catalog(args.output, payload)
    print(f"Wrote {len(records)} catalog entries to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
