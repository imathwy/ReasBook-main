#!/usr/bin/env bash

# Build Verso site and place API docs at _site/docs.
set -euo pipefail

./build.sh
./scripts/build_reasbook_web.sh
./scripts/assemble_site_docs.sh
