#!/usr/bin/env bash

# Decompress previously compressed build subdirectories (ir, literate) in a
# persistent lake cache. Companion to compress_persistent_cache.sh.
#
# Usage: decompress_persistent_cache.sh <lake_dir>
#   <lake_dir>  Path to the persistent lake directory (e.g. /data/cache/v4.30.0/reasbook_lake)

set -euo pipefail

LAKE_DIR="${1:-}"
if [ -z "$LAKE_DIR" ] || [ ! -d "$LAKE_DIR" ]; then
  echo "usage: decompress_persistent_cache.sh <lake_dir>" >&2
  exit 1
fi

BUILD_DIR="$LAKE_DIR/build"
if [ ! -d "$BUILD_DIR" ]; then
  echo "[decompress_cache] no build dir at $BUILD_DIR; skipping"
  exit 0
fi

decompress_subdir() {
  local subdir="$1"
  local target="$BUILD_DIR/$subdir"
  local archive="$BUILD_DIR/${subdir}.tar.zst"

  if [ -d "$target" ]; then
    echo "[decompress_cache] $target already exists (uncompressed); skipping"
    return 0
  fi

  if [ ! -f "$archive" ]; then
    echo "[decompress_cache] no archive at $archive; skipping"
    return 0
  fi

  local archive_size
  archive_size=$(du -sm "$archive" 2>/dev/null | cut -f1)
  echo "[decompress_cache] decompressing $archive (${archive_size:-?} MB) -> $target"

  tar --zstd -xf "$archive" -C "$BUILD_DIR" 2>/dev/null

  local target_size
  target_size=$(du -sm "$target" 2>/dev/null | cut -f1)
  echo "[decompress_cache] decompressed: ${archive_size:-?} MB -> ${target_size:-?} MB"
}

decompress_subdir "ir"
decompress_subdir "literate"

echo "[decompress_cache] done"