#!/usr/bin/env bash

# Publish doc-gen output into the web artifact directory.
#
# The operation is staged in a temporary directory and then renamed into place
# so a running server never observes a half-copied documentation tree.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "$SCRIPT_DIR/common.sh"
REASBOOK_SITE_DIR="${REASBOOK_SITE_DIR:-$REASBOOK_WEB_ROOT/_site}"
export REASBOOK_REPO_ROOT REASBOOK_LEAN_ROOT REASBOOK_SITE_DIR
PYTHON_BIN="$REASBOOK_TOOLING_ROOT/sdk/common/bin/python"

source_docs_dir="${REASBOOK_DOC_SOURCE:-$REASBOOK_DOC_BUILD_DIR/doc}"
docs_index_dir="$REASBOOK_SITE_DIR/docs"
web_docs_dir="$docs_index_dir/ReasBook"

if [[ ! -d "$source_docs_dir" ]]; then
  reasbook_die "missing docs directory: $source_docs_dir"
  exit 1
fi

mkdir -p "$REASBOOK_SITE_DIR"
stage_root="$(mktemp -d "$REASBOOK_SITE_DIR/.docs-stage.XXXXXX")"
cleanup() {
  rm -rf "$stage_root"
}
trap cleanup EXIT

mkdir -p "$stage_root/docs/ReasBook"
cp -a "$source_docs_dir/." "$stage_root/docs/ReasBook/"
find "$stage_root/docs/ReasBook" -type f \( -name '*.trace' -o -name '*.hash' \) -delete

# doc-gen may rewrite absolute links as "../.././/<repo>/..."; normalize these
# back to site-root links before publishing.
site_root="${REASBOOK_SITE_ROOT:-/ReasBook/}"
site_root="${site_root%/}/"
repo_name="${site_root#/}"
repo_name="${repo_name%/}"
if [[ -n "$repo_name" ]]; then
  REASBOOK_DOCS_STAGE="$stage_root/docs/ReasBook" \
  REASBOOK_SITE_REPO="$repo_name" \
  "$PYTHON_BIN" - <<'PY'
from __future__ import annotations

import os
from pathlib import Path
import re

root = Path(os.environ["REASBOOK_DOCS_STAGE"])
repo = re.escape(os.environ["REASBOOK_SITE_REPO"])
patterns = (
    (re.compile(r'href="(?:\.\./)+\.//' + repo + r'/'), 'href="/' + os.environ["REASBOOK_SITE_REPO"] + '/'),
    (re.compile(r'href="(?:\.\./)+' + repo + r'/'), 'href="/' + os.environ["REASBOOK_SITE_REPO"] + '/'),
)
for html in root.rglob("*.html"):
    text = html.read_text(encoding="utf-8", errors="replace")
    for pattern, replacement in patterns:
        text = pattern.sub(replacement, text)
    html.write_text(text, encoding="utf-8")
PY
fi

mkdir -p "$stage_root/docs"
REASBOOK_DOCS_STAGE="$stage_root/docs/ReasBook" \
REASBOOK_DOCS_INDEX="$stage_root/docs/index.html" \
"$PYTHON_BIN" - <<'PY'
from __future__ import annotations

import html
import os
from pathlib import Path

root = Path(os.environ["REASBOOK_DOCS_STAGE"])
index = Path(os.environ["REASBOOK_DOCS_INDEX"])
entries: list[tuple[str, str]] = []
seen: set[Path] = set()

selected = []
for value in os.environ.get("REASBOOK_INCLUDE_PROJECTS", "").split(","):
    parts = value.strip().split("/", 1)
    if len(parts) == 2 and parts[0] in {"books", "papers"} and parts[1]:
        selected.append((parts[0], parts[1]))

for kind, project in selected:
    kind_dir = "Books" if kind == "books" else "Papers"
    leaf = "Book.html" if kind == "books" else "Paper.html"
    candidates = (
        root / kind_dir / project / leaf,
        root / project / leaf,
        root / f"{project}.html",
    )
    candidate = next((path for path in candidates if path.is_file()), None)
    if candidate is None or candidate in seen:
        continue
    seen.add(candidate)
    relative = candidate.relative_to(root).as_posix()
    entries.append((project, f"./ReasBook/{relative}"))

if not selected:
    candidates = (
        sorted(root.glob("Books/*/Book.html"))
        + sorted(root.glob("Papers/*/Paper.html"))
        + sorted(root.glob("*/Book.html"))
        + sorted(root.glob("*/Paper.html"))
    )
    for candidate in candidates:
        if candidate in seen:
            continue
        seen.add(candidate)
        relative = candidate.relative_to(root).as_posix()
        entries.append((candidate.parent.name, f"./ReasBook/{relative}"))

entries.sort(key=lambda item: item[0].lower())

items = "\n".join(
    f'    <li><a href="{html.escape(url, quote=True)}">{html.escape(name)}</a></li>'
    for name, url in entries
)
if not items:
    items = '    <li><span>No generated project documentation yet.</span></li>'
content = f'''<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>ReasBook Documentation</title>
</head>
<body>
  <h1>ReasBook Documentation</h1>
  <ul>
{items}
  </ul>
</body>
</html>
'''
index.write_text(content, encoding="utf-8")
PY

# Replace only the generated docs subtree. Keep the rest of the Verso site (if
# any) intact, and roll back the old subtree if the final rename fails.
mkdir -p "$docs_index_dir"
old_dir=""
if [[ -e "$web_docs_dir" ]]; then
  old_dir="$docs_index_dir/.ReasBook.previous.$$"
  mv "$web_docs_dir" "$old_dir"
fi
old_index=""
if [[ -e "$docs_index_dir/index.html" ]]; then
  old_index="$docs_index_dir/.index.previous.$$"
  mv "$docs_index_dir/index.html" "$old_index"
fi
if mv "$stage_root/docs/ReasBook" "$web_docs_dir"; then
  :
else
  if [[ -n "$old_dir" && -e "$old_dir" ]]; then
    mv "$old_dir" "$web_docs_dir"
  fi
  if [[ -n "$old_index" && -e "$old_index" ]]; then
    mv "$old_index" "$docs_index_dir/index.html"
  fi
  reasbook_die "could not publish documentation subtree"
  exit 1
fi
if ! mv "$stage_root/docs/index.html" "$docs_index_dir/index.html"; then
  rm -rf "$web_docs_dir"
  if [[ -n "$old_dir" && -e "$old_dir" ]]; then
    mv "$old_dir" "$web_docs_dir"
  fi
  if [[ -n "$old_index" && -e "$old_index" ]]; then
    mv "$old_index" "$docs_index_dir/index.html"
  fi
  reasbook_die "could not publish documentation index"
  exit 1
fi
if [[ -n "$old_dir" ]]; then
  rm -rf "$old_dir"
fi
if [[ -n "$old_index" ]]; then
  rm -f "$old_index"
fi

reasbook_log "published docs to $web_docs_dir"
