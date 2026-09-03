#!/usr/bin/env bash

# Build Verso site and place API docs at _site/docs.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "$SCRIPT_DIR/common.sh"
cd "$REASBOOK_REPO_ROOT"

"$SCRIPT_DIR/all.sh"
"$SCRIPT_DIR/verso.sh"
"$SCRIPT_DIR/publish_docs.sh"
