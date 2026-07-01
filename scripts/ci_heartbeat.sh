#!/usr/bin/env bash

# Run a command while emitting periodic heartbeat lines.
set -euo pipefail

if [ "$#" -lt 2 ]; then
  echo "usage: $0 <label> <command> [args...]" >&2
  exit 2
fi

label="$1"
shift
interval="${HEARTBEAT_INTERVAL_SECONDS:-60}"
start_epoch="$(date +%s)"
last_heartbeat_epoch="$start_epoch"
pid=""

on_term() {
  if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; then
    echo "[ci][$label] received termination signal, forwarding to child pid=$pid"
    kill "$pid" 2>/dev/null || true
  fi
}

trap on_term INT TERM

echo "::group::$label"
echo "[ci][$label] start $(date -u +'%Y-%m-%dT%H:%M:%SZ')"

"$@" &
pid="$!"

set +e
while kill -0 "$pid" 2>/dev/null; do
  sleep 1
  now_epoch="$(date +%s)"
  if [ "$((now_epoch - last_heartbeat_epoch))" -ge "$interval" ]; then
    last_heartbeat_epoch="$now_epoch"
    if kill -0 "$pid" 2>/dev/null; then
      elapsed="$((now_epoch - start_epoch))"
      echo "[ci][$label] heartbeat elapsed=${elapsed}s"
    fi
  fi
done

wait "$pid"
status="$?"
set -e

end_epoch="$(date +%s)"
elapsed="$((end_epoch - start_epoch))"
echo "[ci][$label] end $(date -u +'%Y-%m-%dT%H:%M:%SZ') elapsed=${elapsed}s exit=${status}"
echo "::endgroup::"

exit "$status"
