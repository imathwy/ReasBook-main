#!/usr/bin/env python3
"""Sync per-statement files from ALLBOOKS (repo A) to this repository (repo B).

Copies files directly without reorganization — preserves the original
flat/Items/Roman numeral directory structure from ALLBOOKS.

After copying, generates Book.lean with full import chain so ALL per-statement
files are actually compiled by Lake (not just Book.lean itself).

Key fixes applied during sync:
  1. Directory rename: ALLBOOKS name → ReasBook canonical name
  2. Internal import fix: replace old project prefix with new, preserving
     nested project directories (e.g. `import cartan.I.sec01.X` →
     `import DifferentialForms_Cartan_1970.cartan.I.sec01.X`)
  3. Books-subdirectory prefix fix: files under a `Books/` subdir import
     as `Books.LibName.X` → `LibName.Books.LibName.X`
  4. Digit-filename quoting: filenames starting with digits are wrapped in
     French quotes «» per Lean 4 module naming rules
  5. Book.lean: full import chain of ALL .lean files (only .lake/ and
     nested Book.lean are excluded)

Usage:
    python3 scripts/sync_from_a.py --source /tmp/repo-A --all
    python3 scripts/sync_from_a.py --source /tmp/repo-A --book RiemannSurfaces
    python3 scripts/sync_from_a.py --source /tmp/repo-A --all --dry-run
"""

import argparse
import json
import os
import re
import shutil
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from lib.project_scope import clear_degradation

REPO_ROOT = SCRIPT_DIR.parent
BOOKS_DIR = REPO_ROOT / "ReasBook" / "Books"
DEGRADATIONS = REPO_ROOT / "docs" / "degradations.json"


def _clear_degradation(book_name: str, manifest_path: Path = DEGRADATIONS) -> bool:
    """Compatibility wrapper for book sync's canonical degradation clearing."""
    if manifest_path != DEGRADATIONS:
        # Tests and callers may supply an isolated manifest path.
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
        entries = data.get("entries", [])
        data["entries"] = [
            entry for entry in entries
            if not (entry.get("kind") == "book" and entry.get("name") == book_name)
        ]
        changed = len(data["entries"]) != len(entries)
        if changed:
            manifest_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        return changed
    return clear_degradation(REPO_ROOT, "book", book_name)

# ---------------------------------------------------------------------------
# ALLBOOKS source dir → ReasBook target dir (final canonical names)
# ---------------------------------------------------------------------------
DIR_MAP = {
    "JPMay":                                  "AlgebraicTopology_May_1999",
    "AchimKlenke_runner":                     "ProbabilityTheory_Klenke_2020",
    "Bauschke_runner":                        "ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017",
    "cartan":                                 "DifferentialForms_Cartan_1970",
    "chapter1_reference_format_20260519_statement": "chapter1_reference_format",
    "CombinatorialGroupTheory":               "CombinatorialGroupTheory_Magnus_2004",
    "FirstOrderMethodsinOptimization":        "FirstOrderMethodsOptimization_Beck_2017",
    "Nesterov":                               "LecturesConvexOptimization_Nesterov_2018",
    "RiemannSurfaces":                        "RiemannSurfaces_Forster_1981",
    "serre":                                  "LinearRepresentations_Serre_1977",
    "SmoothManifoldsLee":                     "SmoothManifolds_Lee_2012",
    "stacks-refine-stmt":                     "StacksProject_2024",
    "stacks-proof":                           "stacks_proof",
}

# ---------------------------------------------------------------------------
# Old project name → new ReasBook library name.
# The old name is the Lean project name used in `import` statements inside
# the ALLBOOKS source files (e.g. `import cartan.I.section01.Definition_1_1`).
# ---------------------------------------------------------------------------
NAME_MAP = {
    "MayConciseRevised":              "AlgebraicTopology_May_1999",
    "AchimKlenkeLean":                "ProbabilityTheory_Klenke_2020",
    "BauschkeLean":                   "ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017",
    "cartan":                         "DifferentialForms_Cartan_1970",
    "CombinatorialGroupTheory":       "CombinatorialGroupTheory_Magnus_2004",
    "FirstOrderMethodsinOptimization":"FirstOrderMethodsOptimization_Beck_2017",
    "Nesterov":                       "LecturesConvexOptimization_Nesterov_2018",
    "Reaslib":                        "ReasLib",
    "RiemannSurfaces":                "RiemannSurfaces_Forster_1981",
    "Serre":                          "LinearRepresentations_Serre_1977",
    "SmoothManifoldsLee":             "SmoothManifolds_Lee_2012",
    "stacks_project":                 "StacksProject_2024",
}

# ===================================================================
# Helper: French-quote a filename segment that starts with a digit
# ===================================================================
def _lean_module_name(filename: str) -> str:
    """Convert a filesystem filename to a valid Lean 4 module name segment.

    Filenames starting with a digit must be wrapped in French quotes «».
    Examples:
        '0001_Definition_X'  → '«0001_Definition_X»'
        'Definition_1_1'     → 'Definition_1_1'
    """
    if filename and filename[0].isdigit():
        return f"«{filename}»"
    return filename


def _file_to_module(book_dir: Path, file_path: Path, book_name: str) -> str:
    """Convert a .lean file to its full Lean module name (import string).

    This is the SINGLE CANONICAL way to build module names from file paths.
    Handles directory-level modules (Chap06.lean → Chap06, not Chap06.lean),
    digit-starting filenames (0001_X → «0001_X»), and nested directories.

    Examples:
        stacks_project/Chap04/Definition_4_2_1.lean
        → stacks_proof.stacks_project.Chap04.Definition_4_2_1

        stacks_project/Chap04/4_34_2_1.lean
        → stacks_proof.stacks_project.Chap04.«4_34_2_1»
    """
    rel = file_path.relative_to(book_dir)
    parts = list(rel.parts)
    module_segments = []
    for i, part in enumerate(parts):
        if i == len(parts) - 1:
            stem = Path(part).stem  # remove .lean
        else:
            stem = part
        module_segments.append(_lean_module_name(stem))
    return f"{book_name}.{'.'.join(module_segments)}"


def _find_import_line(book_lean_content: str, module_name: str) -> str | None:
    """Find the active import line for a given module in Book.lean content.

    Returns the exact import line string, or None if not found.
    Matches both active and commented-out imports.
    """
    target = f"import {module_name}"
    for line in book_lean_content.split('\n'):
        stripped = line.strip()
        if stripped == target:
            return line
        # Also match commented-out: "-- import ..."
        if stripped == f"-- {target}":
            return line
    return None


# ===================================================================
# Book.lean generation — full import chain, import ALL .lean files
# ===================================================================
def _generate_book_lean(
    book_dir: Path, book_name: str,
) -> int:
    """Generate Book.lean with imports for ALL .lean files in the book.

    Every .lean file under the book directory is imported, regardless of its
    role (per-statement, old project root, scratch, temp, config).  This
    ensures Lake compiles the complete content as originally present in
    ALLBOOKS — no file is silently orphaned.

    Only two categories are excluded:
      - ``.lake/`` directories (build artifacts, not source)
      - other ``Book.lean`` files (avoid self-import and nested-project loops)

    Normal synchronization always restores the complete active import set.
    """
    lake_marker = f"{os.sep}.lake{os.sep}"
    book_lean = book_dir / "Book.lean"

    imports = ["import Mathlib"]
    for f in sorted(book_dir.rglob("*.lean")):
        if lake_marker in f"{f}{os.sep}":
            continue
        if f.name == "Book.lean" and f.parent == book_dir:
            continue
        if f.name == "Book.lean":
            continue

        full_module = _file_to_module(book_dir, f, book_name)

        imports.append(f"import {full_module}")

    book_lean.write_text("\n".join(imports) + "\n", encoding="utf-8")
    return len(imports) - 1


# ===================================================================
# Internal import path fix — preserves nested project directories
# ===================================================================
def _fix_internal_imports(book_dir: Path, old_name: str, new_name: str) -> int:
    """Fix per-statement files' internal imports to use the new book name.

    ALLBOOKS files import each other using the original project name, e.g.:
        import cartan.I.section01.Definition_1_1

    After directory rename, these imports must be updated.  If the book
    directory contains a subdirectory whose name matches *old_name* (the
    nested-project pattern, e.g. ``cartan/cartan/``), the replacement
    preserves that directory prefix:

        import cartan.I.section01.X
        → import DifferentialForms_Cartan_1970.cartan.I.section01.X

    Otherwise the replacement is a flat rename:

        import RiemannSurfaces.Chap01.X
        → import RiemannSurfaces_Forster_1981.Chap01.X
    """
    # Detect nested project directory
    has_nested = (book_dir / old_name).is_dir()

    fixed = 0
    for sf in book_dir.rglob("*.lean"):
        if sf.name == "Book.lean":
            continue
        content = sf.read_text(encoding="utf-8")
        if f"import {old_name}." not in content:
            continue

        if has_nested:
            # Preserve the nested directory in the import path
            content = content.replace(
                f"import {old_name}.",
                f"import {new_name}.{old_name}.",
            )
        else:
            content = content.replace(
                f"import {old_name}.",
                f"import {new_name}.",
            )
        sf.write_text(content, encoding="utf-8")
        fixed += 1
    return fixed


# ===================================================================
# Books-subdirectory prefix fix
# ===================================================================
def _fix_books_prefix_imports(book_dir: Path, book_name: str) -> int:
    """Fix imports in books that have a nested ``Books/<ProjectName>/`` directory.

    Some ALLBOOKS projects (Analysis2, JiriLebl) use:
        Books/
          <ProjectName>/
            Chapters/...

    Files inside import each other as ``Books.<ProjectName>.Chapters.X``.
    The correct import under our naming is:
        ``<BookName>.Books.<ProjectName>.Chapters.X``

    This function rewrites the prefix.
    """
    books_dir = book_dir / "Books"
    if not books_dir.is_dir():
        return 0

    # Find the inner project name (only subdir of Books/)
    inner_names = [
        d.name for d in books_dir.iterdir()
        if d.is_dir() and not d.name.startswith(".")
    ]
    if not inner_names:
        return 0

    fixed = 0
    for inner_name in inner_names:
        old_prefix = f"import Books.{inner_name}."
        new_prefix = f"import {book_name}.Books.{inner_name}."
        inner_dir = books_dir / inner_name
        for sf in inner_dir.rglob("*.lean"):
            if sf.name == "Book.lean":
                continue
            content = sf.read_text(encoding="utf-8")
            if old_prefix not in content:
                continue
            content = content.replace(old_prefix, new_prefix)
            sf.write_text(content, encoding="utf-8")
            fixed += 1
    return fixed


# ===================================================================
# Double book-name fix (Rockafellar / chapter1_ref pattern)
# ===================================================================
def _fix_double_name_imports(book_dir: Path, book_name: str) -> int:
    """Fix imports that accidentally repeat the book name twice.

    Some ALLBOOKS files import with a doubled prefix, e.g.:
        import ConvexAnalysis_Rockafellar_1970.ConvexAnalysis_Rockafellar_1970.Chap01.X
    which should be:
        import ConvexAnalysis_Rockafellar_1970.Chap01.X

    This happens when the old project root file name matches the book name.
    """
    double_prefix = f"{book_name}.{book_name}."
    fixed = 0
    for sf in book_dir.rglob("*.lean"):
        if sf.name == "Book.lean":
            continue
        content = sf.read_text(encoding="utf-8")
        if f"import {double_prefix}" not in content:
            continue
        content = content.replace(f"import {double_prefix}", f"import {book_name}.")
        sf.write_text(content, encoding="utf-8")
        fixed += 1
    return fixed


# ===================================================================
# ALLBOOKS project artifact cleanup
# ===================================================================

# Root-level files that are ALLBOOKS project config (not Lean source)
_ARTIFACT_FILES = {
    "lakefile.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
}

# Root-level directories that are non-Lean metadata
_ARTIFACT_DIRS = {
    "source_data",
}


def _cleanup_book_dir(book_dir: Path) -> int:
    """Remove ALLBOOKS project config files and non-Lean directories.

    Each book was originally its own Lake project in ALLBOOKS.  After
    copying into the unified ReasBook workspace, the per-book
    ``lakefile.*``, ``lake-manifest.json``, ``lean-toolchain`` and
    ``source_data/`` are dead artifacts — the root-level
    ``ReasBook/lakefile.lean`` and ``ReasBook/lean-toolchain`` control
    the build.

    Returns the number of files/directories removed.
    """
    removed = 0
    for name in _ARTIFACT_FILES:
        path = book_dir / name
        if path.is_file():
            path.unlink()
            removed += 1
    for name in _ARTIFACT_DIRS:
        path = book_dir / name
        if path.is_dir():
            shutil.rmtree(path)
            removed += 1
    return removed


# ===================================================================
# Main sync for a single book
# ===================================================================

# ===================================================================
# Cross-book import fix (stacks_proof pattern)
# ===================================================================
def _fix_cross_book_imports(book_dir: Path, book_name: str) -> int:
    """Fix imports that accidentally reference a different book's library.

    When two ALLBOOKS projects share a common internal project name (e.g.
    ``stacks_project``), _fix_internal_imports replaces both with the same
    target name.  But the second book (stacks_proof) should reference its
    own copy of that namespace, not the other book's library.

    This function detects the pattern and reassigns the imports.
    """
    # Known cross-book patterns: old_name that maps to a DIFFERENT library
    # from the one a given book should use.
    CROSS_BOOK_MAP = {
        "stacks_proof": {
            "StacksProject_2024": "stacks_proof.stacks_project",
        }
    }

    if book_name not in CROSS_BOOK_MAP:
        return 0

    fixed = 0
    replacements = CROSS_BOOK_MAP[book_name]
    for wrong_prefix, correct_prefix in replacements.items():
        old_import = f"import {wrong_prefix}."
        new_import = f"import {correct_prefix}."
        for sf in book_dir.rglob("*.lean"):
            if sf.name == "Book.lean":
                continue
            content = sf.read_text(encoding="utf-8")
            if old_import not in content:
                continue
            content = content.replace(old_import, new_import)
            sf.write_text(content, encoding="utf-8")
            fixed += 1
    return fixed


def sync_book(source_repo: Path, dir_name: str, dry_run: bool):
    """Copy per-statement files from A to B, fix imports, generate Book.lean."""
    src_dir = source_repo / dir_name
    if not src_dir.exists():
        print(f"  Source not found: {src_dir}")
        return

    b_name = DIR_MAP.get(dir_name, dir_name)
    dst_dir = BOOKS_DIR / b_name

    if dry_run:
        print(f"  [DRY RUN] {src_dir} → {dst_dir}")
        return

    # 1. Copy the entire directory tree
    if dst_dir.exists():
        shutil.rmtree(dst_dir)
    shutil.copytree(src_dir, dst_dir)
    count = len(list(dst_dir.rglob("*.lean")))
    print(f"  Synced: {dir_name} → {b_name} ({count} .lean files)")

    # 2. Fix internal import paths (preserving nested project dirs)
    for old, new in NAME_MAP.items():
        # Skip entries where old name doesn't appear in source path
        if old not in str(src_dir):
            continue
        imp_fixed = _fix_internal_imports(dst_dir, old, new)
        if imp_fixed:
            print(f"    Fixed {imp_fixed} internal imports ({old} → {new})")

    # 3. Fix Books-subdirectory prefix (Analysis2, JiriLebl pattern)
    books_fixed = _fix_books_prefix_imports(dst_dir, b_name)
    if books_fixed:
        print(f"    Fixed {books_fixed} Books-subdirectory imports")

    # 4. Fix double book-name imports (Rockafellar / chapter1_ref pattern)
    double_fixed = _fix_double_name_imports(dst_dir, b_name)
    if double_fixed:
        print(f"    Fixed {double_fixed} double-name imports")

    # 5. Fix cross-book imports (stacks_proof → StacksProject_2024 pattern)
    cross_fixed = _fix_cross_book_imports(dst_dir, b_name)
    if cross_fixed:
        print(f"    Fixed {cross_fixed} cross-book imports")

    # 6. Clean up ALLBOOKS project artifacts (lakefile, lean-toolchain, source_data)
    cleaned = _cleanup_book_dir(dst_dir)
    if cleaned:
        print(f"    Cleaned {cleaned} ALLBOOKS project artifact(s)")

    # 7. Generate Book.lean with full import chain
    book_imports = _generate_book_lean(dst_dir, b_name)
    print(f"    Book.lean: {book_imports} imports (full chain)")
    if _clear_degradation(b_name):
        print("    Cleared temporary degradation approval for full revalidation")


# ===================================================================
# CLI
# ===================================================================
def main():
    parser = argparse.ArgumentParser(
        description="Sync files from ALLBOOKS to ReasBook"
    )
    parser.add_argument("--source", required=True, help="Path to ALLBOOKS clone")
    parser.add_argument("--all", action="store_true", help="Sync all books")
    parser.add_argument("--book", help="Sync a specific ALLBOOKS directory")
    parser.add_argument("--dry-run", action="store_true", help="Preview only")
    args = parser.parse_args()

    source = Path(args.source)
    if not source.exists():
        print(f"ERROR: Source not found: {source}", file=sys.stderr)
        sys.exit(1)

    if args.book:
        sync_book(source, args.book, args.dry_run)
    elif args.all:
        for d in sorted(source.iterdir()):
            if d.is_dir() and any(d.rglob("*.lean")):
                sync_book(source, d.name, args.dry_run)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
