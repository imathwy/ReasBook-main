#!/usr/bin/env bash

# Build the Verso web project after sections/routes generation.
set -euo pipefail

HOME_DIR="${HOME:-/root}"
LAKE_BIN="${LAKE_BIN:-$HOME_DIR/.elan/bin/lake}"

echo "[build_reasbook_web] generating sections/routes"
cd ReasBookWeb
python3 scripts/gen_sections.py

# ReasBookWeb depends on Verso/subverso/MD4Lean and does not expose the
# Mathlib `cache` executable. Cache priming is handled in ReasBook scripts.
echo "[build_reasbook_web] skipping cache get (no `lake exe cache` in ReasBookWeb)"

echo "[build_reasbook_web] building Verso site"
"$LAKE_BIN" exe reasbook-site
