#!/usr/bin/env bash

# Build the ReasBook site and start the container.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SITE_DIR="$ROOT_DIR/ReasBookWeb/_site"

cd "$ROOT_DIR"
./build-web.sh

[ -f "$SITE_DIR/index.html" ] || {
  echo "[deploy.sh] missing $SITE_DIR/index.html" >&2
  exit 1
}

docker compose up -d --build
