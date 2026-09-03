#!/usr/bin/env bash

# Build the main Lean project.
#
# BUILD_DOCS:
#   unset -> automatically enabled when doc-gen4 is registered
#   1     -> build docs
#   0     -> skip docs
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "$SCRIPT_DIR/common.sh"

# Detect documentation support automatically unless explicitly overridden.
if [ -z "${BUILD_DOCS+x}" ]; then
  if grep -Eq \
    '^[[:space:]]*require[[:space:]].*doc-gen4' \
    "$REASBOOK_LEAN_ROOT/lakefile.lean"
  then
    BUILD_DOCS=1
  else
    BUILD_DOCS=0
  fi
fi

reasbook_log "phase: cache get"
"$SCRIPT_DIR/cache.sh"

# Build Lean first.
#
# There is no reason to spend tens of minutes generating documentation
# before discovering that the actual project does not compile.
reasbook_log "phase: core build"
"$SCRIPT_DIR/core.sh"

if [ "$BUILD_DOCS" = "1" ]; then
  reasbook_log "phase: shared docs"
  "$SCRIPT_DIR/shared_docs.sh"

  reasbook_log "phase: project docs"
  "$SCRIPT_DIR/project_docs.sh"
else
  reasbook_log "docs disabled or unavailable; skipping"
fi

reasbook_log "build complete"
