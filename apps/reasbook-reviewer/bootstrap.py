"""Expose the repository's SDK packages to source-based app entry points."""

from pathlib import Path
import sys


REPOSITORY = Path(__file__).resolve().parents[2]
for source in sorted((REPOSITORY / "sdk").glob("*/src")):
    if str(source) not in sys.path:
        sys.path.insert(0, str(source))
