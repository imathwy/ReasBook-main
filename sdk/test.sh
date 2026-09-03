#!/usr/bin/env bash

# Run every capability SDK's offline test suite with one shared import path.
set -euo pipefail

SDK_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PYTHON_BIN="$SDK_ROOT/common/bin/python"

export PYTHONPATH="$SDK_ROOT/common/src:$SDK_ROOT/build/src:$SDK_ROOT/verso/src:$SDK_ROOT/theorem_graph/src:$SDK_ROOT/comparator/src:$SDK_ROOT/deploy/src${PYTHONPATH:+:$PYTHONPATH}"

"$PYTHON_BIN" -m unittest discover -s "$SDK_ROOT/common/tests" -v

for suite in build verso theorem_graph comparator deploy; do
  "$PYTHON_BIN" -m unittest discover -s "$SDK_ROOT/$suite/tests" -v
done
