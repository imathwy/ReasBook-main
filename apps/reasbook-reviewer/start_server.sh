#!/usr/bin/env bash
set -euo pipefail
REVIEWER_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$REVIEWER_DIR"

REVIEWER_PYTHON="${REASBOOK_REVIEWER_PYTHON:-${REASBOOK_PYTHON_BIN:-python3}}"
if [[ -z "${REASBOOK_REVIEWER_PYTHON:-}${REASBOOK_PYTHON_BIN:-}" && -x .venv/bin/python ]]; then
  REVIEWER_PYTHON=.venv/bin/python
elif [[ -z "${REASBOOK_REVIEWER_PYTHON:-}${REASBOOK_PYTHON_BIN:-}" && -x .python311/bin/python ]]; then
  REVIEWER_PYTHON=.python311/bin/python
fi

exec "$REVIEWER_PYTHON" - <<'PY'
import os
from pathlib import Path
import sys

if sys.version_info < (3, 11):
    raise SystemExit("ReasBook Reviewer requires Python 3.11 or newer")

# Share the SDK's non-executable .env parser; explicit process settings win.
import bootstrap  # noqa: F401
from reasbook_deploy_sdk.runtime import read_env_defaults

for key, value in read_env_defaults(Path(".env")).items():
    os.environ.setdefault(key, value)

import uvicorn

port = int(os.environ.get("REASBOOK_REVIEWER_PORT", "8876"))
if not 1 <= port <= 65535:
    raise SystemExit("REASBOOK_REVIEWER_PORT must be between 1 and 65535")
uvicorn.run(
    "app:app", host=os.environ.get("REASBOOK_REVIEWER_HOST", "127.0.0.1"), port=port,
    workers=1, forwarded_allow_ips=os.environ.get("FORWARDED_ALLOW_IPS", "127.0.0.1"),
)
PY
