#!/usr/bin/env bash

# Prime Lean cache artifacts for ReasBook.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LAKE_BIN="${LAKE_BIN:-$(command -v lake)}"

echo "[build_reasbook_cache] $(date -u +'%Y-%m-%dT%H:%M:%SZ') running cache get"
cd "$ROOT_DIR/ReasBook"
"$LAKE_BIN" exe cache get
