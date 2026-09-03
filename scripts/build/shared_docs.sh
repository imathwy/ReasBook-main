#!/usr/bin/env bash

# Build shared ReasBook API docs in module chunks.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "$SCRIPT_DIR/common.sh"

cd "$REASBOOK_LEAN_ROOT"

if ! grep -Eq '^[[:space:]]*require[[:space:]].*doc-gen4' lakefile.lean; then
  echo "[build_reasbook_shared_docs] doc-gen4 is not registered; skipping"
  exit 0
fi

declare -a modules=()
BUILD_SDK="$REASBOOK_TOOLING_ROOT/sdk/build/bin/reasbook-build"
if [[ ! -x "$BUILD_SDK" ]]; then
  reasbook_die "build SDK entrypoint is missing: $BUILD_SDK"
  exit 2
fi
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
  reasbook_log "building ${mod}:docs"
  reasbook_run_runtime "$REASBOOK_LEAN_ROOT" \
    "$BUILD_SDK" build "$REASBOOK_LEAN_ROOT" "${mod}:docs" \
    --lake-arg=-R --lake-arg=-Kenv=dev --skip-cache-get --no-verify-outputs
done
