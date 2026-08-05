#!/usr/bin/env bash

# Copy doc-gen output into ReasBookWeb/_site/docs and ensure docs index exists.
set -euo pipefail

web_docs_dir="ReasBookWeb/_site/docs"
source_docs_dir="ReasBook/.lake/build/doc"

if [ ! -d "$source_docs_dir" ]; then
  echo "[assemble_site_docs] missing docs directory: $source_docs_dir" >&2
  exit 1
fi

mkdir -p "$web_docs_dir"
cp -r "$source_docs_dir"/. "$web_docs_dir"/
find "$web_docs_dir" -name "*.trace" -delete || true
find "$web_docs_dir" -name "*.hash" -delete || true

# doc-gen may rewrite absolute links as "../.././/<repo>/..."; normalize
# these back to site-root absolute links so aggregate pages navigate correctly.
site_root="${REASBOOK_SITE_ROOT:-/ReasBook/}"
site_root="${site_root%/}/"
repo_name="${site_root#/}"
repo_name="${repo_name%/}"
if [ -n "$repo_name" ]; then
  escaped_repo_name="$(printf '%s' "$repo_name" | sed -e 's/[.[\*^$()+?{}|/]/\\&/g')"
  find "$web_docs_dir" -type f -name "*.html" -print0 \
    | xargs -0 perl -0777 -i -pe \
      "s#href=\"(?:\\.\\./)+\\.//${escaped_repo_name}/#href=\"/${repo_name}/#g; s#href=\"(?:\\.\\./)+${escaped_repo_name}/#href=\"/${repo_name}/#g"
fi

if [ ! -f "$web_docs_dir/index.html" ]; then
  cat > "$web_docs_dir/index.html" <<'EOF'
<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>ReasBook Documentation</title>
</head>
<body>
  <h1>ReasBook Documentation</h1>
  <ul>
    <li><a href="./Books/FirstOrderMethodsInOptimization_Beck_2017/Book.html">First-Order Methods in Optimization (Beck, 2017)</a></li>
  </ul>
</body>
</html>
EOF
fi
