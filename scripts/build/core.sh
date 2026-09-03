#!/usr/bin/env bash

# Build the main Lean target through sdk/build.
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "$SCRIPT_DIR/common.sh"

build_sdk="$REASBOOK_TOOLING_ROOT/sdk/build/bin/reasbook-build"
if [[ ! -x "$build_sdk" ]]; then
  reasbook_die "build SDK entrypoint is missing: $build_sdk"
  exit 2
fi

declare -a targets=()
if [[ -n "${REASBOOK_LAKE_TARGETS:-}" ]]; then
  while IFS= read -r item; do
    item="$(printf '%s' "$item" | xargs)"
    [[ -n "$item" ]] && targets+=("$item")
  done < <(printf '%s\n' "$REASBOOK_LAKE_TARGETS" | tr ',' '\n')
fi

args=(build "$REASBOOK_LEAN_ROOT")
if [[ ${#targets[@]} -gt 0 ]]; then
  args+=("${targets[@]}")
fi
args+=(--lake-arg=-R --no-verify-outputs)
reasbook_log "running sdk/build core plan"
reasbook_run_runtime "$REASBOOK_LEAN_ROOT" "$build_sdk" "${args[@]}"
