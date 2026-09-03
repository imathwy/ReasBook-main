#!/usr/bin/env bash

# Repository paths and logging shared by the build adapters. Runtime policy
# belongs to sdk/deploy runtime, not to this shell layer.

if [[ "${REASBOOK_BUILD_COMMON_LOADED:-0}" == "1" ]]; then
  return 0 2>/dev/null || exit 0
fi
REASBOOK_BUILD_COMMON_LOADED=1

REASBOOK_TOOLING_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
REASBOOK_REPO_ROOT="${REASBOOK_REPO_ROOT:-$REASBOOK_TOOLING_ROOT}"
REASBOOK_LEAN_ROOT="${REASBOOK_LEAN_ROOT:-$REASBOOK_REPO_ROOT/ReasBook}"
REASBOOK_WEB_ROOT="${REASBOOK_WEB_ROOT:-$REASBOOK_REPO_ROOT/ReasBookWeb}"
export REASBOOK_REPO_ROOT REASBOOK_LEAN_ROOT REASBOOK_WEB_ROOT

reasbook_log() {
  printf '[reasbook] %s %s\n' "$(date -u +'%Y-%m-%dT%H:%M:%SZ')" "$*"
}

reasbook_die() {
  printf '[reasbook] ERROR: %s\n' "$*" >&2
  return 1
}

reasbook_run_runtime() {
  local project="$1"
  shift
  local -a runtime_args=(runtime "$project")
  if [[ -n "${REASBOOK_RUNTIME_CACHE_PREFIX:-}" ]]; then
    runtime_args+=(--cache-prefix "$REASBOOK_RUNTIME_CACHE_PREFIX")
  fi
  if [[ "${REASBOOK_USE_EXTERNAL_CACHE:-1}" == "0" ]]; then
    runtime_args+=(--no-link-lake)
  fi
  if [[ "${REASBOOK_FORCE_EXTERNAL_CACHE:-0}" == "1" ]]; then
    runtime_args+=(--force-external-lake)
  fi
  "$REASBOOK_TOOLING_ROOT/sdk/deploy/bin/reasbook-deploy" \
    "${runtime_args[@]}" -- "$@"
}
