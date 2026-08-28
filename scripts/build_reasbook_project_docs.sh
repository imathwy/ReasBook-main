#!/usr/bin/env bash

# Build docs for registered book/paper projects.
#
# Supported layouts:
#
# v4.26-style:
#   lean_lib Books where
#   lean_lib Papers where
#
#   -> build module targets such as
#      Books.Analysis2_Tao_2022.Book:docs
#
# v4.30+-style:
#   lean_lib Analysis2_Tao_2022 where
#     srcDir := "Books"
#
#   -> build library target
#      Analysis2_Tao_2022:docs
#
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HOME_DIR="${HOME:-/root}"
LAKE_BIN="${LAKE_BIN:-$HOME_DIR/.elan/bin/lake}"

cd "$ROOT_DIR/ReasBook"

# doc-gen4 is required for the :docs facet.
if ! grep -Eq '^[[:space:]]*require[[:space:]].*doc-gen4' lakefile.lean; then
  echo "[build_reasbook_project_docs] doc-gen4 is not registered; skipping"
  exit 0
fi

declare -a targets=()

# Explicit override remains supported.
if [ -n "${PROJECT_DOC_MODULES:-}" ]; then
  while IFS= read -r item; do
    item="$(printf '%s' "$item" | xargs)"
    [ -n "$item" ] || continue
    targets+=("$item")
  done < <(printf '%s\n' "$PROJECT_DOC_MODULES" | tr ',' '\n')
else
  # Read the actual Lake layout instead of guessing the Lean target
  # directly from the filesystem path.
  mapfile -t targets < <(
    python3 - <<'PY'
import re
from pathlib import Path

lakefile = Path("lakefile.lean")
lines = lakefile.read_text(encoding="utf-8").splitlines()

def uncomment(line: str) -> str:
    # Only line comments are relevant in the current lakefiles.
    return line.split("--", 1)[0].rstrip()

def normalize_name(name: str) -> str:
    name = name.strip()
    if name.startswith("«") and name.endswith("»"):
        name = name[1:-1]
    if name.startswith('"') and name.endswith('"'):
        name = name[1:-1]
    return name

aggregate = {
    "Books": False,
    "Papers": False,
}

flat = {
    "Books": [],
    "Papers": [],
}

for i, raw in enumerate(lines):
    code = uncomment(raw)

    m = re.match(r'^\s*lean_lib\s+(\S+)\s+where\b', code)
    if not m:
        continue

    name = normalize_name(m.group(1))

    src_dir = None

    # lean_lib declarations in this repository are top-level and their
    # options are indented underneath them.
    j = i + 1
    while j < len(lines):
        next_raw = lines[j]
        next_code = uncomment(next_raw)

        if not next_code.strip():
            j += 1
            continue

        # A new non-indented declaration ends this lean_lib block.
        if next_raw and not next_raw[0].isspace():
            break

        m_src = re.match(
            r'^\s*srcDir\s*:=\s*"([^"]+)"',
            next_code
        )
        if m_src:
            src_dir = m_src.group(1)

        j += 1

    if name in aggregate and src_dir is None:
        aggregate[name] = True

    if src_dir in flat:
        flat[src_dir].append(name)

targets = []

for kind, leaf in (
    ("Books", "Book"),
    ("Papers", "Paper"),
):
    if aggregate[kind]:
        # Old v4.26-style aggregate library.
        #
        # Example:
        #   Books/Analysis2_Tao_2022/Book.lean
        # ->
        #   Books.Analysis2_Tao_2022.Book
        for path in sorted(Path(kind).glob(f"*/{leaf}.lean")):
            target = str(path.with_suffix("")).replace("/", ".")
            targets.append(target)
    else:
        # v4.30+-style one-library-per-project.
        #
        # Build the registered library itself rather than guessing a
        # module from Books/... or Papers/....
        targets.extend(flat[kind])

seen = set()

for target in targets:
    if target in seen:
        continue
    seen.add(target)
    print(target)
PY
  )
fi

if [ "${#targets[@]}" -eq 0 ]; then
  echo "[build_reasbook_project_docs] no registered project doc targets found"
  exit 0
fi

for target in "${targets[@]}"; do
  echo "[build_reasbook_project_docs] $(date -u +'%Y-%m-%dT%H:%M:%SZ') building ${target}:docs"
  "$LAKE_BIN" -R -Kenv=dev build "${target}:docs"
done