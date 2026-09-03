#!/usr/bin/env bash

# Generate sections and build the Verso site through sdk/verso.
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "$SCRIPT_DIR/common.sh"

VERSO_SDK="$REASBOOK_TOOLING_ROOT/sdk/verso/bin/verso-build"
if [[ ! -x "$VERSO_SDK" ]]; then
  reasbook_die "Verso SDK entrypoint is missing: $VERSO_SDK"
  exit 2
fi

export VERSO_WEB_ROOT="$REASBOOK_WEB_ROOT"
export VERSO_TARGETS="exe reasbook-site"
if [[ -n "${REASBOOK_VERSO_GENERATOR:-}" ]]; then
  generator_args=(
    "$REASBOOK_TOOLING_ROOT/sdk/common/bin/python"
    "$REASBOOK_VERSO_GENERATOR"
    --repo-root
    "$REASBOOK_REPO_ROOT"
  )
  printf -v VERSO_GENERATOR '%q ' "${generator_args[@]}"
  export VERSO_GENERATOR
  export VERSO_GENERATOR_CWD="$REASBOOK_REPO_ROOT"
else
  export VERSO_GENERATOR="$REASBOOK_TOOLING_ROOT/sdk/common/bin/python scripts/gen_sections.py"
  export VERSO_GENERATOR_CWD="$REASBOOK_WEB_ROOT"
fi
export VERSO_OUTPUT_DIR="$REASBOOK_WEB_ROOT/_site"
export VERSO_VERIFY_OUTPUT=1

if ulimit -s unlimited 2>/dev/null; then
  echo "[build_reasbook_web] stack limit set to unlimited"
fi
reasbook_log "running sdk/verso pipeline"
REASBOOK_RUNTIME_CACHE_PREFIX=web- \
  reasbook_run_runtime "$REASBOOK_WEB_ROOT" "$VERSO_SDK" "$REASBOOK_WEB_ROOT"
