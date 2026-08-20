#!/usr/bin/env bash

# Compress heavy build subdirectories (ir, literate) in a persistent lake cache
# to save disk space. These directories contain C compilation artifacts and
# literate JSON dumps that are large but highly compressible text.
#
# Usage: compress_persistent_cache.sh <lake_dir>
#   <lake_dir>  Path to the persistent lake directory (e.g. /data/cache/v4.30.0/reasbook_lake)

set -euo pipefail

LAKE_DIR="${1:-}"
if [ -z "$LAKE_DIR" ] || [ ! -d "$LAKE_DIR" ]; then
  echo "usage: compress_persistent_cache.sh <lake_dir>" >&2
  exit 1
fi

BUILD_DIR="$LAKE_DIR/build"
if [ ! -d "$BUILD_DIR" ]; then
  echo "[compress_cache] no build dir at $BUILD_DIR; skipping"
  exit 0
fi

compress_subdir() {
  local subdir="$1"
  local target="$BUILD_DIR/$subdir"
  local archive="$BUILD_DIR/${subdir}.tar.zst"

  if [ ! -d "$target" ]; then
    echo "[compress_cache] $target does not exist; skipping"
    return 0
  fi

  local before
  before=$(du -sm "$target" 2>/dev/null | cut -f1)
  echo "[compress_cache] compressing $target (${before:-?} MB) -> $archive"

  tar --zstd -cf "$archive" -C "$BUILD_DIR" "$subdir" 2>/dev/null
  local after
  after=$(du -sm "$archive" 2>/dev/null | cut -f1)
  echo "[compress_cache] compressed: ${before:-?} MB -> ${after:-?} MB"

  rm -rf "$target"
  echo "[compress_cache] removed uncompressed $target"
}

compress_subdir "ir"
compress_subdir "literate"

echo "[compress_cache] done"