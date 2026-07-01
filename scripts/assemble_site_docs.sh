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
    <li><a href="./Books/Analysis2_Tao_2022/Chapters/Chap01/section01.html">Analysis II (Tao): Chapter 1 Section 1</a></li>
    <li><a href="./Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap01/section01_part1.html">Convex Analysis (Rockafellar): Chapter 1 Section 1 Part 1</a></li>
    <li><a href="./Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap01/section01.html">Introduction to Real Analysis I (Lebl): Chapter 1 Section 1</a></li>
    <li><a href="./Papers/SmoothMinimization_Nesterov_2004/Sections/section01.html">Nesterov 2004: Section 1</a></li>
    <li><a href="./Papers/OnSomeLocalRings_Maassaran_2025/Sections/section01.html">Maassarani 2025: Section 1</a></li>
  </ul>
</body>
</html>
EOF
fi
