#!/usr/bin/env bash

# Build bounded-memory docs for registered book/paper project roots.
#
# Supported layouts:
#
# v4.26-style:
#   lean_lib Books where
#   lean_lib Papers where
#
#   -> build module targets such as
#      Books.Analysis2_Tao_2022.Book:docs
#
# v4.30+-style:
#   lean_lib Analysis2_Tao_2022 where
#     srcDir := "Books"
#
#   -> build library target
#      Analysis2_Tao_2022:docs
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "$SCRIPT_DIR/common.sh"

cd "$REASBOOK_LEAN_ROOT"

# doc-gen4 is required for the :docs facet.
if ! grep -Eq '^[[:space:]]*require[[:space:]].*doc-gen4' lakefile.lean; then
  echo "[build_reasbook_project_docs] doc-gen4 is not registered; skipping"
  exit 0
fi

declare -a targets=()
BUILD_SDK="$REASBOOK_TOOLING_ROOT/sdk/build/bin/reasbook-build"
if [[ ! -x "$BUILD_SDK" ]]; then
  reasbook_die "build SDK entrypoint is missing: $BUILD_SDK"
  exit 2
fi
# Release/deploy callers pass their immutable profile selection through
# REASBOOK_LAKE_TARGETS. When that variable is present, it takes precedence
# over ambient operator settings and automatic discovery so profile exclusions
# cannot be silently reintroduced.
if [[ -v REASBOOK_LAKE_TARGETS ]]; then
  while IFS= read -r item; do
    item="$(printf '%s' "$item" | xargs)"
    [ -n "$item" ] || continue
    targets+=("$item")
  done < <(printf '%s\n' "$REASBOOK_LAKE_TARGETS" | tr ',' '\n')
  if [ "${#targets[@]}" -eq 0 ]; then
    reasbook_die \
      "REASBOOK_LAKE_TARGETS is set but contains no documentation roots" || exit 2
  fi
elif [ -n "${PROJECT_DOC_MODULES:-}" ]; then
  while IFS= read -r item; do
    item="$(printf '%s' "$item" | xargs)"
    [ -n "$item" ] || continue
    targets+=("$item")
  done < <(printf '%s\n' "$PROJECT_DOC_MODULES" | tr ',' '\n')
else
  mapfile -t targets < <(
    "$BUILD_SDK" targets "$REASBOOK_LEAN_ROOT" \
      --mode project-docs
  )
fi

if [ "${#targets[@]}" -eq 0 ]; then
  echo "[build_reasbook_project_docs] no registered project doc targets found"
  exit 0
fi

declare -a docs_args=(
  project-docs "$REASBOOK_LEAN_ROOT"
  "${targets[@]}"
  --output "$REASBOOK_DOC_BUILD_DIR"
  --lake-bin "${REASBOOK_BUILD_LAKE_BIN:-${LAKE_BIN:-lake}}"
  --timeout-seconds "${REASBOOK_DOC_COMMAND_TIMEOUT:-21600}"
)
if [[ -n "${REASBOOK_SOURCE_REPOSITORY:-}" || -n "${REASBOOK_SOURCE_COMMIT:-}" ]]; then
  docs_args+=(
    --repository "${REASBOOK_SOURCE_REPOSITORY:-}"
    --revision "${REASBOOK_SOURCE_COMMIT:-}"
  )
fi

reasbook_log "building compact API docs for ${#targets[@]} project root(s)"
reasbook_run_runtime "$REASBOOK_LEAN_ROOT" "$BUILD_SDK" "${docs_args[@]}"
