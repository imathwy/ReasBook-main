#!/usr/bin/env bash

# Remove generated artifacts from git tracking without deleting local files.
# Run from repository root.
set -euo pipefail

git rm -r --cached --ignore-unmatch ReasBook/.lake
find ReasBook -type d -name .lake -print0 | xargs -0 -r git rm -r --cached --ignore-unmatch

git rm -r --cached --ignore-unmatch ReasBookWeb/.lake
git rm -r --cached --ignore-unmatch ReasBookWeb/_site
git rm -r --cached --ignore-unmatch ReasBookWeb/-verso-*
git rm -r --cached --ignore-unmatch ReasBookWeb/Book

echo "Cleanup staged. Next steps:"
echo "  1) git status"
echo "  2) git commit -m 'Stop tracking generated artifacts'"
echo "If large generated files are already deep in git history, use git filter-repo separately."
