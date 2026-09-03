#!/usr/bin/env bash

# Build docs for registered book/paper projects.
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
# Explicit override remains supported.
if [ -n "${PROJECT_DOC_MODULES:-}" ]; then
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

for target in "${targets[@]}"; do
  reasbook_log "building ${target}:docs"
  reasbook_run_runtime "$REASBOOK_LEAN_ROOT" \
    "$BUILD_SDK" build "$REASBOOK_LEAN_ROOT" "${target}:docs" \
    --lake-arg=-R --lake-arg=-Kenv=dev --skip-cache-get --no-verify-outputs
done
