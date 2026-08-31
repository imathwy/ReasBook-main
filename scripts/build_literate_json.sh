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
FAILED_FILE="$WEB_DIR/.literate_failed.txt"
STATUS_FILE="$WEB_DIR/.literate_status.json"
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
ok=0
: > "$FAILED_FILE"

# Mirror buildLiterateJsonChunk's environment scrub so the nested Lake build
# selects the toolchain requested by ReasBook/lean-toolchain.
SCRUB_ENV=(
  env -u LAKE -u LAKE_HOME -u LAKE_PKG_URL_MAP
      -u LEAN_SYSROOT -u LEAN_AR -u LEAN_PATH -u LEAN_SRC_PATH
      -u LEAN_GITHASH -u ELAN_TOOLCHAIN -u DYLD_LIBRARY_PATH -u LD_LIBRARY_PATH
)

BATCH_SIZE="${REASBOOK_LITERATE_BATCH_SIZE:-100}"

build_one() {
  local mod="$1" rc=0
  set +e
  (cd "$REASBOOK_DIR" && timeout --kill-after=30 "${TIMEOUT_MINUTES}m" \
      "${SCRUB_ENV[@]}" "$ELAN_BIN" run --install "$toolchain" lake build "+${mod}:literate")
  rc=$?
  set -e
  return "$rc"
}

record_failure() {
  local mod="$1" rc="$2"
  failed=$((failed + 1))
  if [[ "$rc" -eq 124 || "$rc" -eq 137 ]]; then
    echo "[literate] TIMEOUT ${mod}"
    echo "::warning title=Literate extraction timed out::${mod}"
  else
    echo "[literate] FAILED ${mod}"
    echo "::error title=Literate extraction failed::${mod}"
  fi
  echo "$mod" >> "$FAILED_FILE"
}

mapfile -t modules < <(grep -vE '^\s*$' "$MODULES_FILE")
count=${#modules[@]}

for ((start = 0; start < count; start += BATCH_SIZE)); do
  batch=("${modules[@]:start:BATCH_SIZE}")

  if [[ "${#batch[@]}" -eq 1 ]]; then
    mod="${batch[0]}"
    echo "[literate] start ${mod}"
    if build_one "$mod"; then
      ok=$((ok + 1))
      echo "[literate] ok ${mod}"
    else
      record_failure "$mod" "$?"
    fi
    continue
  fi

  args=()
  for mod in "${batch[@]}"; do
    args+=("+${mod}:literate")
  done
  echo "[literate] batch start ${#batch[@]} modules (${batch[0]} .. ${batch[-1]})"

  set +e
  (cd "$REASBOOK_DIR" && timeout --kill-after=30 "$((TIMEOUT_MINUTES * 2))m" \
      "${SCRUB_ENV[@]}" "$ELAN_BIN" run --install "$toolchain" lake build "${args[@]}")
  rc=$?
  set -e

  if [[ "$rc" -eq 0 ]]; then
    ok=$((ok + ${#batch[@]}))
    echo "[literate] batch ok ${#batch[@]}"
    continue
  fi

  echo "[literate] batch failed (rc=${rc}); isolating ${#batch[@]} modules"
  for mod in "${batch[@]}"; do
    echo "[literate] start ${mod}"
    if build_one "$mod"; then
      ok=$((ok + 1))
      echo "[literate] ok ${mod}"
    else
      record_failure "$mod" "$?"
    fi
  done
done

python3 - "$STATUS_FILE" "$FAILED_FILE" "$count" "$ok" "$failed" <<'PY'
import json
import sys
from pathlib import Path

status_file = Path(sys.argv[1])
failed_file = Path(sys.argv[2])
count = int(sys.argv[3])
ok = int(sys.argv[4])
failed = int(sys.argv[5])

failed_modules = [
    line.strip()
    for line in failed_file.read_text(encoding="utf-8").splitlines()
    if line.strip()
]
status_file.write_text(
    json.dumps(
        {
            "count": count,
            "ok": ok,
            "failed": failed,
            "failed_modules": failed_modules,
        },
        ensure_ascii=True,
        indent=2,
    )
    + "\n",
    encoding="utf-8",
)
PY

echo "[literate] ${ok} ok, ${failed} failed, ${count} total"

if [[ "$failed" -ne 0 && "${REASBOOK_LITERATE_FAIL_FAST:-0}" == "1" ]]; then
  echo "[literate] fail-fast requested; exiting with failure" >&2
  exit 1
fi

exit 0
