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
LITERATE_SDK="$REASBOOK_TOOLING_ROOT/sdk/verso/bin/verso-literate"
if [[ ! -x "$LITERATE_SDK" ]]; then
  reasbook_die "Verso literate cache entrypoint is missing: $LITERATE_SDK"
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
else
  generator_args=(
    "$REASBOOK_TOOLING_ROOT/sdk/common/bin/python"
    "$REASBOOK_WEB_ROOT/scripts/gen_sections.py"
    --repo-root
    "$REASBOOK_REPO_ROOT"
  )
fi

reasbook_log "generating Verso sections and literate module manifest"
(
  cd "$REASBOOK_REPO_ROOT"
  "${generator_args[@]}"
)

LITERATE_MANIFEST="$REASBOOK_WEB_ROOT/.literate-modules.json"
if [[ ! -f "$LITERATE_MANIFEST" || -L "$LITERATE_MANIFEST" ]]; then
  reasbook_die "Literate module manifest is missing or unsafe: $LITERATE_MANIFEST"
  exit 2
fi
reasbook_log "completing identity-bound literate cache"
REASBOOK_RUNTIME_CACHE_PREFIX= \
  reasbook_run_runtime "$REASBOOK_LEAN_ROOT" "$LITERATE_SDK" \
  --lean-root "$REASBOOK_LEAN_ROOT" \
  --module-manifest "$LITERATE_MANIFEST"

# Branch-specific Lake files only skip their nested extraction loop after the
# SDK has validated every artifact and atomically committed its completion
# marker.  The generator already ran above, so the generic Verso SDK must not
# run it a second time.
export REASBOOK_LITERATE_PREBUILT=1
export VERSO_ENV_REASBOOK_LITERATE_PREBUILT=1
export VERSO_GENERATOR=""
export VERSO_GENERATOR_CWD="$REASBOOK_REPO_ROOT"
export VERSO_OUTPUT_DIR="$REASBOOK_WEB_ROOT/_site"
export VERSO_VERIFY_OUTPUT=1

if ulimit -s unlimited 2>/dev/null; then
  echo "[build_reasbook_web] stack limit set to unlimited"
fi
reasbook_log "running sdk/verso pipeline"
REASBOOK_RUNTIME_CACHE_PREFIX=web- \
  reasbook_run_runtime "$REASBOOK_WEB_ROOT" "$VERSO_SDK" "$REASBOOK_WEB_ROOT"
