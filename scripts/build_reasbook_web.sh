#!/usr/bin/env bash

# Build the Verso web project after sections/routes generation.
set -euo pipefail

HOME_DIR="${HOME:-/root}"
LAKE_BIN="${LAKE_BIN:-$HOME_DIR/.elan/bin/lake}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

echo "[build_reasbook_web] generating sections/routes"
cd "$REPO_ROOT/ReasBookWeb"
python3 scripts/gen_sections.py
cd "$REPO_ROOT"

echo "[build_reasbook_web] extracting literate JSON per module"
./scripts/build_literate_json.sh

echo "[build_reasbook_web] regenerating sections/routes from literate status"
cd "$REPO_ROOT/ReasBookWeb"
python3 scripts/gen_sections.py
cd "$REPO_ROOT"

cd "$REPO_ROOT/ReasBookWeb"

# ReasBookWeb depends on Verso/subverso/MD4Lean and does not expose the
# Mathlib `cache` executable. Cache priming is handled in ReasBook scripts.
echo "[build_reasbook_web] skipping cache get (no 'lake exe cache' in ReasBookWeb)"

echo "[build_reasbook_web] building Verso site"
if ulimit -s unlimited 2>/dev/null; then
  echo "[build_reasbook_web] stack limit set to unlimited"
else
  echo "[build_reasbook_web] unable to raise stack limit; continuing with current limit"
fi
REASBOOK_LITERATE_PREBUILT=1 "$LAKE_BIN" exe reasbook-site
