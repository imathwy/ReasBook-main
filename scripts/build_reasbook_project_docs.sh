#!/usr/bin/env bash

# Build docs for each book/paper root module.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HOME_DIR="${HOME:-/root}"
LAKE_BIN="${LAKE_BIN:-$HOME_DIR/.elan/bin/lake}"

cd "$ROOT_DIR/ReasBook"

declare -a modules=()

if [ -n "${PROJECT_DOC_MODULES:-}" ]; then
  while IFS= read -r item; do
    [ -n "$item" ] || continue
    modules+=("$item")
  done < <(printf '%s\n' "$PROJECT_DOC_MODULES" | tr ',' '\n')
else
  for entry in Books/*/Book.lean Papers/*/Paper.lean; do
    [ -f "$entry" ] || continue
    mod="${entry%.lean}"
    mod="${mod//\//.}"
    modules+=("$mod")
  done
fi

if [ "${#modules[@]}" -eq 0 ]; then
  echo "[build_reasbook_project_docs] no project modules found"
  exit 0
fi

for mod in "${modules[@]}"; do
  echo "[build_reasbook_project_docs] $(date -u +'%Y-%m-%dT%H:%M:%SZ') building ${mod}:docs"
  "$LAKE_BIN" -R -Kenv=dev build "$mod:docs"
done
