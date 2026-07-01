#!/usr/bin/env bash

# Build the main ReasBook Lean target.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HOME_DIR="${HOME:-/root}"
LAKE_BIN="${LAKE_BIN:-$HOME_DIR/.elan/bin/lake}"

echo "[build_reasbook_core] $(date -u +'%Y-%m-%dT%H:%M:%SZ') running lake build"
cd "$ROOT_DIR/ReasBook"
"$LAKE_BIN" build
