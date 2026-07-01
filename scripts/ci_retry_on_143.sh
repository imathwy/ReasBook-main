#!/usr/bin/env bash

# Retry a command once when it exits with code 143 (SIGTERM).
set -euo pipefail

if [ "$#" -lt 1 ]; then
  echo "usage: $0 <command> [args...]" >&2
  exit 2
fi

max_retries="${RETRY_ON_143_MAX_RETRIES:-1}"
sleep_seconds="${RETRY_ON_143_SLEEP_SECONDS:-15}"
attempt=1
max_attempts="$((max_retries + 1))"

while true; do
  echo "[ci][retry143] attempt ${attempt}/${max_attempts}"

  set +e
  "$@"
  status="$?"
  set -e

  if [ "$status" -eq 0 ]; then
    exit 0
  fi

  if [ "$status" -eq 143 ] && [ "$attempt" -lt "$max_attempts" ]; then
    echo "[ci][retry143] command exited 143; retrying after ${sleep_seconds}s"
    sleep "$sleep_seconds"
    attempt="$((attempt + 1))"
    continue
  fi

  echo "[ci][retry143] command failed with exit=${status}; no more retries"
  exit "$status"
done
