#!/usr/bin/env bash

# Prime Lean cache artifacts through sdk/build.
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "$SCRIPT_DIR/common.sh"

if [[ "${REASBOOK_SKIP_CACHE_GET:-0}" == "1" ]]; then
  reasbook_log "cache get disabled by REASBOOK_SKIP_CACHE_GET"
  exit 0
fi

BUILD_SDK="$REASBOOK_TOOLING_ROOT/sdk/build/bin/reasbook-build"
if [[ ! -x "$BUILD_SDK" ]]; then
  reasbook_die "build SDK entrypoint is missing: $BUILD_SDK"
  exit 2
fi

cache_timeout="${REASBOOK_CACHE_TIMEOUT:-300}"
if [[ ! "$cache_timeout" =~ ^[1-9][0-9]*([.][0-9]+)?$ ]]; then
  reasbook_die "REASBOOK_CACHE_TIMEOUT must be a positive number of seconds"
  exit 2
fi

declare -a targets=()
if [[ -n "${REASBOOK_CACHE_TARGETS:-}" ]]; then
  while IFS= read -r item; do
    [[ -n "$item" ]] && targets+=("$item")
  done < <(printf '%s\n' "$REASBOOK_CACHE_TARGETS" | tr ', ' '\n')
fi

args=(
  cache "$REASBOOK_LEAN_ROOT"
)
if [[ ${#targets[@]} -gt 0 ]]; then
  args+=("${targets[@]}")
fi
args+=(--lake-arg=-R --cache-timeout-seconds "$cache_timeout")
if ! reasbook_run_runtime "$REASBOOK_LEAN_ROOT" "$BUILD_SDK" "${args[@]}"; then
  if [[ "${REASBOOK_CACHE_GET_REQUIRED:-0}" == "1" ]]; then
    reasbook_die "Lake cache get failed"
    exit 1
  fi
  reasbook_log "cache get failed; local compilation will continue"
fi
