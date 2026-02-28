#!/usr/bin/env bash

# Build docs/core targets for selected books/papers from PROJECTS_JSON.
set -euo pipefail

HOME_DIR="${HOME:-/root}"
LAKE_BIN="${LAKE_BIN:-$HOME_DIR/.elan/bin/lake}"
PROJECTS_JSON="${PROJECTS_JSON:-[]}"

cd ReasBook

mapfile -t targets < <(
  PROJECTS_JSON="$PROJECTS_JSON" python3 - <<'PY'
import json
import os

projects = json.loads(os.environ.get("PROJECTS_JSON", "[]"))
seen = set()
targets = []
for p in projects:
    kind = p.get("kind")
    name = p.get("name")
    if not kind or not name:
        continue
    if kind == "books":
        root = f"Books.{name}.Book"
    elif kind == "papers":
        root = f"Papers.{name}.Paper"
    else:
        continue
    for target in (f"{root}:docs", root):
        if target not in seen:
            seen.add(target)
            targets.append(target)

for t in targets:
    print(t)
PY
)

if [ "${#targets[@]}" -eq 0 ]; then
  echo "[build_selected_projects] no selected project targets; skipping"
  exit 0
fi

echo "[build_selected_projects] building ${#targets[@]} targets"
for t in "${targets[@]}"; do
  echo "[build_selected_projects] target: $t"
done

"$LAKE_BIN" -R -Kenv=dev build "${targets[@]}"
