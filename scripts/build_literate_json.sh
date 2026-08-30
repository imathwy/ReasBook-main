#!/usr/bin/env bash

# Extract each ReasBook module's Verso literate JSON independently.
#
# This is intentionally run outside Lake's target graph. Lake buffers target
# output until the target finishes, so a single slow/hung module previously
# hid all progress and eventually exhausted the job timeout. Running the same
# `+<module>:literate` builds directly here makes the last-started module
# visible in CI and bounds each module with its own timeout.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WEB_DIR="$REPO_ROOT/ReasBookWeb"
REASBOOK_DIR="$REPO_ROOT/ReasBook"
MODULES_FILE="$WEB_DIR/.literate_modules.txt"
ELAN_BIN="${ELAN_BIN:-${HOME:-/root}/.elan/bin/elan}"
TIMEOUT_MINUTES="${REASBOOK_LITERATE_TIMEOUT_MINUTES:-10}"

if [[ ! -f "$MODULES_FILE" ]]; then
  echo "[literate] generating sections and module manifest" >&2
  (cd "$WEB_DIR" && python3 scripts/gen_sections.py)
fi

if [[ ! -f "$MODULES_FILE" ]]; then
  echo "[literate] missing module manifest: $MODULES_FILE" >&2
  exit 1
fi

toolchain="$(tr -d '\r\n' < "$REASBOOK_DIR/lean-toolchain")"
if [[ -z "$toolchain" ]]; then
  echo "[literate] empty toolchain in $REASBOOK_DIR/lean-toolchain" >&2
  exit 1
fi

count=0
failed=0

while IFS= read -r mod; do
  [[ -z "$mod" ]] && continue
  count=$((count + 1))
  echo "[literate] start ${mod}"

  # Mirror buildLiterateJsonChunk's environment scrub so the nested Lake build
  # selects the toolchain requested by ReasBook/lean-toolchain.
  if (cd "$REASBOOK_DIR" && timeout --kill-after=30 "${TIMEOUT_MINUTES}m" \
      env -u LAKE -u LAKE_HOME -u LAKE_PKG_URL_MAP \
          -u LEAN_SYSROOT -u LEAN_AR -u LEAN_PATH -u LEAN_SRC_PATH \
          -u LEAN_GITHASH -u ELAN_TOOLCHAIN -u DYLD_LIBRARY_PATH -u LD_LIBRARY_PATH \
      "$ELAN_BIN" run --install "$toolchain" lake build "+${mod}:literate"); then
    echo "[literate] ok ${mod}"
  else
    failed=$((failed + 1))
    echo "[literate] FAILED ${mod}"
    echo "::error title=Literate extraction failed::${mod}"
    break
  fi
done < "$MODULES_FILE"

if [[ "$failed" -ne 0 ]]; then
  echo "[literate] ${failed} module(s) failed after processing ${count} module(s)" >&2
  exit "$failed"
fi

echo "[literate] extracted ${count} module(s)"
