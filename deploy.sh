#!/usr/bin/env bash

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SITE_DIR="$ROOT_DIR/ReasBookWeb/_site"

cd "$ROOT_DIR"

if [ ! -f "$SITE_DIR/index.html" ]; then
  echo "[deploy.sh] missing $SITE_DIR/index.html" >&2
  echo "[deploy.sh] build or prepare ReasBookWeb/_site before deployment" >&2
  exit 1
fi

if ! command -v docker >/dev/null 2>&1; then
  echo "[deploy.sh] docker is not installed" >&2
  exit 1
fi

if ! docker compose version >/dev/null 2>&1; then
  echo "[deploy.sh] docker compose is not available" >&2
  exit 1
fi

docker compose up -d --build

echo "[deploy.sh] deployment complete"
echo "[deploy.sh] port: ${REASBOOK_PORT:-3200}"
