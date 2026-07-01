#!/usr/bin/env bash

# Build the main Lean project. Set BUILD_DOCS=0 to skip doc-gen4.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BUILD_DOCS="${BUILD_DOCS:-1}"

log() {
  echo "[build.sh] $(date -u +'%Y-%m-%dT%H:%M:%SZ') $*"
}

log "phase: cache get"
"$ROOT_DIR/scripts/build_reasbook_cache.sh"

if [ "$BUILD_DOCS" = "1" ]; then
  log "phase: shared docs"
  "$ROOT_DIR/scripts/build_reasbook_shared_docs.sh"
  log "phase: project docs"
  "$ROOT_DIR/scripts/build_reasbook_project_docs.sh"
fi

log "phase: core build"
"$ROOT_DIR/scripts/build_reasbook_core.sh"
log "build complete"
