#!/usr/bin/env bash

# Build shared ReasBook API docs in module chunks.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HOME_DIR="${HOME:-/root}"
LAKE_BIN="${LAKE_BIN:-$HOME_DIR/.elan/bin/lake}"

cd "$ROOT_DIR/ReasBook"

declare -a modules=()

# Default to a valid shared baseline module.
raw_modules="${SHARED_DOC_MODULES:-ReasBook}"
while IFS= read -r item; do
  item="$(printf '%s' "$item" | xargs)"
  [ -n "$item" ] || continue
  modules+=("$item")
done < <(printf '%s\n' "$raw_modules" | tr ',' '\n')

if [ "${#modules[@]}" -eq 0 ]; then
  echo "[build_reasbook_shared_docs] no shared doc modules configured; skipping"
  exit 0
fi

for mod in "${modules[@]}"; do
  echo "[build_reasbook_shared_docs] $(date -u +'%Y-%m-%dT%H:%M:%SZ') building ${mod}:docs"
  "$LAKE_BIN" -R -Kenv=dev build "${mod}:docs"
done
