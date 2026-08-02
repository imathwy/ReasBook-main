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
    python3 scripts/sync_from_a.py --source /tmp/repo-A --all --dry-run
    python3 scripts/sync_from_a.py --source /tmp/repo-A --book RiemannSurfaces --dry-run
    python3 scripts/sync_from_a.py --source /tmp/repo-A --all --dry-run

The historical delete-and-copy implementation is permanently retired.  The
``--legacy-destructive-sync`` spelling remains recognized only to return a
clear migration error.  Inventory is read-only, and every mutation must use
the three-way synchronization planner.
"""

import argparse
import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from lib.project_scope import clear_degradation
from lib.sync_three_way import (
    apply_staged_tree, plan_tree_merge, render_tree_diff, tree_hash,
)

REPO_ROOT = SCRIPT_DIR.parent
BOOKS_DIR = REPO_ROOT / "ReasBook" / "Books"
PAPERS_DIR = REPO_ROOT / "ReasBook" / "Papers"
DEGRADATIONS = REPO_ROOT / "scripts" / "state" / "degradations.json"
SYNC_STATE = REPO_ROOT / "scripts" / "state" / "sync-state.json"
NORMALIZATION_PROFILE_VERSION = 1
FLATTEN_SUBDIRECTORY = {
    "chapter1_reference_format_20260519_statement": "chapter1_reference_format",
    "ConvexAnalysis_Rockafellar_1970": "ConvexAnalysis_Rockafellar_1970",
}

PAPER_SOURCE_PROJECTS = {
    "OnSomeLocalRings_Maassaran_2025": "OnSomeLocalRings_Maassaran_2025",
    "SmoothMinimization_Nesterov_2004": "SmoothMinimization_Nesterov_2004",
}


def normalization_profile(dir_name: str) -> dict:
    """Return the complete deterministic normalization profile for one source."""
    return {
        "id": f"{dir_name}-v{NORMALIZATION_PROFILE_VERSION}",
        "version": NORMALIZATION_PROFILE_VERSION,
        "source_directory": dir_name,
        "book_name": DIR_MAP.get(dir_name, dir_name),
        "name_map": dict(sorted(NAME_MAP.items())),
        "artifact_files": sorted(_ARTIFACT_FILES),
        "artifact_directories": sorted(_ARTIFACT_DIRS),
        "flatten_subdirectory": FLATTEN_SUBDIRECTORY.get(dir_name),
        "generate_complete_entry": True,
    }


def paper_normalization_profile(dir_name: str, paper_name: str) -> dict:
    """Return the deterministic normalization profile for one canonical paper."""
    expected = PAPER_SOURCE_PROJECTS.get(dir_name)
    if expected != paper_name:
        raise ValueError(f"ALLBOOKS source {dir_name} does not map to paper:{paper_name}")
    return {
        "id": f"{dir_name}-paper-{paper_name}-v{NORMALIZATION_PROFILE_VERSION}",
        "version": NORMALIZATION_PROFILE_VERSION,
        "source_directory": dir_name,
        "paper_name": paper_name,
        "source_subdirectory": f"Papers/{paper_name}",
        "generate_complete_entry": True,
    }


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

    Every canonical source file under the book directory is imported.  Entry
    modules are retained in the normalized tree but excluded from this book
    boundary, matching ``lib.project_scope.source_files``.

    The excluded categories are:
      - ``.lake/`` directories (build artifacts, not source)
      - ``Book.lean`` and ``Paper.lean`` entry modules (avoid entry cycles and
        cross-boundary extras)

    Normal synchronization always restores the complete active import set.
    """
    lake_marker = f"{os.sep}.lake{os.sep}"
    book_lean = book_dir / "Book.lean"

    imports = ["import Mathlib"]
    for f in sorted(book_dir.rglob("*.lean")):
        if lake_marker in f"{f}{os.sep}":
            continue
        if f.name in {"Book.lean", "Paper.lean"}:
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

    # 1. Copy and deterministically normalize the entire directory tree.
    if dst_dir.exists():
        shutil.rmtree(dst_dir)
    result = normalize_book_tree(src_dir, dst_dir, dir_name)
    count = result["source_count"]
    print(f"  Synced: {dir_name} → {b_name} ({count} .lean files)")
    for message in result["messages"]:
        print(f"    {message}")
    if _clear_degradation(b_name):
        print("    Cleared temporary degradation approval for full revalidation")


def preview_paper(source_repo: Path, dir_name: str, paper_name: str) -> None:
    src_dir = source_repo / dir_name
    if not src_dir.exists():
        print(f"  Source not found: {src_dir}")
        return
    print(f"  [DRY RUN] {src_dir} → {PAPERS_DIR / paper_name}")


def normalize_book_tree(src_dir: Path, dst_dir: Path, dir_name: str) -> dict:
    """Create the canonical byte-stable ReasBook tree for one ALLBOOKS project.

    The destination must not exist.  The function has no repository-global
    side effects: it does not clear degradation state or touch another book.
    """
    if dst_dir.exists():
        raise ValueError(f"normalization destination already exists: {dst_dir}")
    if not src_dir.is_dir():
        raise ValueError(f"ALLBOOKS project does not exist: {src_dir}")
    b_name = DIR_MAP.get(dir_name, dir_name)
    shutil.copytree(src_dir, dst_dir)
    messages: list[str] = []
    source_count = len(list(dst_dir.rglob("*.lean")))

    profile = normalization_profile(dir_name)
    if nested_name := profile["flatten_subdirectory"]:
        nested = dst_dir / nested_name
        if not nested.is_dir():
            raise ValueError(f"normalization profile expects nested directory: {nested_name}")
        for child in sorted(nested.iterdir()):
            if child.name == "Book.lean":
                continue
            destination = dst_dir / child.name
            if destination.exists():
                raise ValueError(f"cannot flatten {nested_name}: duplicate {child.name}")
            child.rename(destination)
        shutil.rmtree(nested)
        messages.append(f"Flattened source directory {nested_name}")
    for old, new in profile["name_map"].items():
        fixed = _fix_internal_imports(dst_dir, old, new)
        if fixed:
            messages.append(f"Fixed {fixed} internal imports ({old} → {new})")
    books_fixed = _fix_books_prefix_imports(dst_dir, b_name)
    if books_fixed:
        messages.append(f"Fixed {books_fixed} Books-subdirectory imports")
    double_fixed = _fix_double_name_imports(dst_dir, b_name)
    if double_fixed:
        messages.append(f"Fixed {double_fixed} double-name imports")
    cross_fixed = _fix_cross_book_imports(dst_dir, b_name)
    if cross_fixed:
        messages.append(f"Fixed {cross_fixed} cross-book imports")
    cleaned = _cleanup_book_dir(dst_dir)
    if cleaned:
        messages.append(f"Cleaned {cleaned} ALLBOOKS project artifact(s)")
    imports = _generate_book_lean(dst_dir, b_name)
    messages.append(f"Book.lean: {imports} imports (full chain)")
    return {
        "source_count": source_count,
        "book_name": b_name,
        "imports": imports,
        "messages": messages,
    }


def normalize_paper_tree(
    src_dir: Path, dst_dir: Path, dir_name: str, paper_name: str,
) -> dict:
    """Create the canonical byte-stable tree for one paper inside an ALLBOOKS project."""
    if dst_dir.exists():
        raise ValueError(f"normalization destination already exists: {dst_dir}")
    profile = paper_normalization_profile(dir_name, paper_name)
    nested = src_dir / profile["source_subdirectory"]
    if not nested.is_dir():
        raise ValueError(
            f"paper source directory is missing at {profile['source_subdirectory']}"
        )
    shutil.copytree(nested, dst_dir)
    source_count = len(list(dst_dir.rglob("*.lean")))
    imports = ["import Mathlib"]
    for path in sorted(dst_dir.rglob("*.lean")):
        if ".lake" in path.parts or path.name in {"Book.lean", "Paper.lean"}:
            continue
        parts = path.relative_to(dst_dir).with_suffix("").parts
        quoted = [f"«{part}»" if part and part[0].isdigit() else part for part in parts]
        imports.append(f"import {'.'.join(('Papers', paper_name, *quoted))}")
    (dst_dir / "Paper.lean").write_text("\n".join(imports) + "\n", encoding="utf-8")
    return {
        "source_count": source_count,
        "paper_name": paper_name,
        "imports": len(imports) - 1,
        "messages": [f"Paper.lean: {len(imports) - 1} imports (full chain)"],
    }


def _scope_details(
    kind: str, dir_name: str, project_name: str | None,
    *, books_dir: Path = BOOKS_DIR, papers_dir: Path = PAPERS_DIR,
) -> tuple[str, str, Path, dict]:
    if kind == "book":
        name = DIR_MAP.get(dir_name, dir_name)
        return name, f"book:{name}", books_dir / name, normalization_profile(dir_name)
    if kind == "paper":
        name = project_name or PAPER_SOURCE_PROJECTS.get(dir_name)
        if not name:
            raise ValueError(f"ALLBOOKS source {dir_name} has no canonical paper mapping")
        return name, f"paper:{name}", papers_dir / name, paper_normalization_profile(dir_name, name)
    raise ValueError(f"unsupported sync project kind: {kind}")


def _normalize_scope(
    source: Path, destination: Path, dir_name: str, kind: str, project_name: str,
) -> dict:
    if kind == "book":
        return normalize_book_tree(source, destination, dir_name)
    return normalize_paper_tree(source, destination, dir_name, project_name)


def _legacy_mode_error(
    *, dry_run: bool, legacy_destructive_sync: bool,
    all_books: bool, destination_exists: bool,
) -> str | None:
    """Reject the retired destructive path while preserving read-only inventory."""
    del all_books, destination_exists
    if legacy_destructive_sync:
        return (
            "--legacy-destructive-sync is permanently retired; use the "
            "three-way synchronization planner"
        )
    if dry_run:
        return None
    return (
        "destructive synchronization is disabled; use --dry-run or the "
        "three-way synchronization planner"
    )


def _git(repo: Path, *args: str, binary: bool = False):
    return subprocess.run(
        ["git", "-C", str(repo), *args], check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=not binary,
    )


def _resolve_commit(repo: Path, revision: str) -> str:
    result = _git(repo, "rev-parse", "--verify", f"{revision}^{{commit}}")
    if result.returncode:
        raise ValueError(
            f"ALLBOOKS revision is not reachable: {revision}: {result.stderr.strip()}"
        )
    return result.stdout.strip()


def _extract_project(repo: Path, commit: str, directory: str, destination: Path) -> Path:
    """Extract exactly one project directory from an ALLBOOKS commit."""
    result = _git(repo, "archive", "--format=tar", commit, directory, binary=True)
    if result.returncode:
        error = result.stderr.decode("utf-8", errors="replace").strip()
        raise ValueError(f"could not archive {directory} at {commit}: {error}")
    destination.mkdir(parents=True, exist_ok=True)
    with tarfile.open(fileobj=io.BytesIO(result.stdout), mode="r:") as archive:
        archive.extractall(destination, filter="data")
    project = destination / directory
    if not project.is_dir():
        raise ValueError(f"ALLBOOKS commit {commit} does not contain {directory}")
    return project


def _git_text(repo: Path, *args: str) -> str:
    result = _git(repo, *args)
    return result.stdout.strip() if result.returncode == 0 else "unknown"


def _worktree_fingerprint(repo: Path) -> str:
    head = _git_text(repo, "rev-parse", "HEAD")
    status = _git(repo, "status", "--porcelain=v1", "--untracked-files=all")
    if status.returncode or not status.stdout.strip():
        return head
    digest = hashlib.sha256()
    digest.update(_git(repo, "diff", "--binary", "HEAD", binary=True).stdout)
    untracked = _git(repo, "ls-files", "--others", "--exclude-standard", "-z", binary=True)
    for raw_name in sorted(filter(None, untracked.stdout.split(b"\0"))):
        digest.update(raw_name)
        path = repo / raw_name.decode("utf-8")
        if path.is_file():
            digest.update(path.read_bytes())
    return f"worktree@{head}:{digest.hexdigest()[:16]}"


def _load_sync_state(path: Path) -> dict:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError(f"could not read sync state {path}: {error}") from error
    if payload.get("schema_version") != 1 or not isinstance(payload.get("projects"), dict):
        raise ValueError("sync-state schema_version must be 1 and projects must be an object")
    return payload


def create_baseline_candidate(
    *, source_repo: Path, dir_name: str, at_commit: str, report_dir: Path,
    kind: str = "book", project_name: str | None = None,
    repo_root: Path = REPO_ROOT, books_dir: Path = BOOKS_DIR,
    papers_dir: Path = PAPERS_DIR,
) -> dict:
    """Compare one normalized ALLBOOKS commit with the current local project."""
    if report_dir.exists():
        raise ValueError(f"baseline report directory already exists: {report_dir}")
    commit = _resolve_commit(source_repo, at_commit)
    name, project_key, target, profile = _scope_details(
        kind, dir_name, project_name, books_dir=books_dir, papers_dir=papers_dir
    )
    if not target.is_dir():
        raise ValueError(f"ReasBook project does not exist: {target}")
    report_dir.mkdir(parents=True)
    try:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = _extract_project(source_repo, commit, dir_name, root / "source")
            normalized = root / "normalized"
            _normalize_scope(source, normalized, dir_name, kind, name)
            normalized_hash = tree_hash(normalized)
            local_hash = tree_hash(target)
            local_diff = render_tree_diff(normalized, target, "normalized-upstream", "local")
        (report_dir / "local.diff").write_text(local_diff, encoding="utf-8")
        candidate = {
            "schema_version": 1,
            "project": project_key,
            "source_directory": dir_name,
            "upstream_commit": commit,
            "normalization_profile": profile["id"],
            "normalizer_commit": _git_text(repo_root, "rev-parse", "HEAD"),
            "normalized_tree_sha256": normalized_hash,
            "local_tree_sha256": local_hash,
            "exact_match": normalized_hash == local_hash,
            "local_diff_sha256": hashlib.sha256(local_diff.encode()).hexdigest(),
            "reasbook_commit": _git_text(repo_root, "rev-parse", "HEAD"),
            "worktree_fingerprint": _worktree_fingerprint(repo_root),
            "accepted": False,
        }
        (report_dir / "baseline-candidate.json").write_text(
            json.dumps(candidate, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
        )
        (report_dir / "summary.md").write_text(
            f"# Baseline candidate for {candidate['project']}\n\n"
            f"- ALLBOOKS commit: `{commit}`\n"
            f"- Normalized tree: `{normalized_hash}`\n"
            f"- Local tree: `{local_hash}`\n"
            f"- Exact match: `{'yes' if candidate['exact_match'] else 'no'}`\n"
            "- Status: `candidate-only`\n",
            encoding="utf-8",
        )
        return candidate
    except Exception:
        shutil.rmtree(report_dir, ignore_errors=True)
        raise


def accept_baseline_candidate(
    candidate_path: Path, state_path: Path, *, reason: str,
    approve_reconciliation: bool = False,
) -> dict:
    """Accept an explicitly reviewed initial baseline into sync provenance."""
    candidate = json.loads(candidate_path.read_text(encoding="utf-8"))
    if candidate.get("schema_version") != 1 or not candidate.get("project"):
        raise ValueError("invalid baseline candidate")
    if candidate.get("accepted"):
        raise ValueError("baseline candidate is already accepted")
    if not reason.strip():
        raise ValueError("baseline acceptance requires a review reason")
    if not candidate.get("exact_match") and not approve_reconciliation:
        raise ValueError(
            "non-exact baseline requires --approve-reconciliation and review of local.diff"
        )
    if state_path.exists():
        state = _load_sync_state(state_path)
    else:
        state = {
            "schema_version": 1,
            "source": {"name": "ALLBOOKS", "url": "https://github.com/wl-ma/ALLBOOKS.git"},
            "projects": {},
        }
    key = candidate["project"]
    if key in state["projects"]:
        raise ValueError(f"sync baseline already exists for {key}")
    state["projects"][key] = {
        "source_directory": candidate["source_directory"],
        "accepted_upstream_commit": candidate["upstream_commit"],
        "normalization_profile": candidate["normalization_profile"],
        "normalizer_commit": candidate["normalizer_commit"],
        "normalized_tree_sha256": candidate["normalized_tree_sha256"],
        "accepted_in_reasbook_commit": candidate["reasbook_commit"],
        "last_sync_report": str(candidate_path.parent),
        "baseline_review_reason": reason.strip(),
        "initial_local_diff_sha256": candidate["local_diff_sha256"],
    }
    state_path.parent.mkdir(parents=True, exist_ok=True)
    state_path.write_text(json.dumps(state, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    candidate["accepted"] = True
    candidate["acceptance_reason"] = reason.strip()
    candidate_path.write_text(
        json.dumps(candidate, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    return state["projects"][key]


def accept_verified_sync(
    plan_path: Path, automation_report: Path, state_path: Path, *, repo_root: Path = REPO_ROOT,
) -> dict:
    """Advance A0 to A1 only after exact single-project full-pass evidence."""
    plan = json.loads(plan_path.read_text(encoding="utf-8"))
    if not plan.get("applied"):
        raise ValueError("sync plan has not been applied")
    lifecycle_path = automation_report / "lifecycle.json"
    lifecycle = json.loads(lifecycle_path.read_text(encoding="utf-8"))
    expected = ("full-pass", "completed", "full-pass")
    actual = (
        lifecycle.get("run_result"), lifecycle.get("session_state"),
        lifecycle.get("project_state"),
    )
    if lifecycle.get("project") != plan.get("project") or actual != expected:
        raise ValueError("automation report does not prove full-pass for the sync project")
    current_head = _git_text(repo_root, "rev-parse", "HEAD")
    if lifecycle.get("target_revision") != current_head:
        raise ValueError("full-pass report does not match the current committed sync tree")
    target = repo_root / plan["target_path"]
    if tree_hash(target) != plan.get("applied_tree_sha256"):
        raise ValueError("current project tree differs from the applied and verified sync plan")
    state = _load_sync_state(state_path)
    entry = state["projects"].get(plan["project"])
    if not entry or entry.get("accepted_upstream_commit") != plan.get("base_upstream_commit"):
        raise ValueError("sync state no longer matches the plan base commit")
    entry.update({
        "accepted_upstream_commit": plan["target_upstream_commit"],
        "normalization_profile": plan["normalization_profile"],
        "normalizer_commit": plan["normalizer_commit"],
        "normalized_tree_sha256": plan["theirs_tree_sha256"],
        "accepted_in_reasbook_commit": current_head,
        "last_sync_report": str(automation_report),
    })
    state_path.write_text(json.dumps(state, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return entry


def create_sync_plan(
    *, source_repo: Path, dir_name: str, to_commit: str, report_dir: Path,
    kind: str = "book", project_name: str | None = None,
    state_path: Path = SYNC_STATE, repo_root: Path = REPO_ROOT,
    books_dir: Path = BOOKS_DIR, papers_dir: Path = PAPERS_DIR,
) -> dict:
    """Create a read-only, exact-commit plan for one canonical book or paper."""
    if report_dir.exists():
        raise ValueError(f"sync report directory already exists: {report_dir}")
    state = _load_sync_state(state_path)
    name, key, target_dir, expected_profile_payload = _scope_details(
        kind, dir_name, project_name, books_dir=books_dir, papers_dir=papers_dir
    )
    project_state = state["projects"].get(key)
    if not isinstance(project_state, dict):
        raise ValueError(f"sync baseline is unresolved for {key}")
    if project_state.get("source_directory") != dir_name:
        raise ValueError(f"sync-state source directory mismatch for {key}")
    profile = project_state.get("normalization_profile")
    expected_profile = expected_profile_payload["id"]
    if profile != expected_profile:
        raise ValueError(
            f"normalization profile mismatch for {key}: expected {expected_profile}, got {profile}"
        )
    base_commit = _resolve_commit(source_repo, project_state["accepted_upstream_commit"])
    target_commit = _resolve_commit(source_repo, to_commit)
    if not target_dir.is_dir():
        raise ValueError(f"ReasBook project does not exist: {target_dir}")
    planned_branch = _git_text(repo_root, "branch", "--show-current")
    planned_head = _git_text(repo_root, "rev-parse", "HEAD")
    planned_fingerprint = _worktree_fingerprint(repo_root)

    report_dir.mkdir(parents=True)
    with tempfile.TemporaryDirectory() as temporary:
        temporary_root = Path(temporary)
        base_source = _extract_project(source_repo, base_commit, dir_name, temporary_root / "base-source")
        target_source = _extract_project(source_repo, target_commit, dir_name, temporary_root / "target-source")
        base_normalized = temporary_root / "base-normalized"
        target_normalized = temporary_root / "target-normalized"
        _normalize_scope(base_source, base_normalized, dir_name, kind, name)
        _normalize_scope(target_source, target_normalized, dir_name, kind, name)
        rebuilt_hash = tree_hash(base_normalized)
        if rebuilt_hash != project_state.get("normalized_tree_sha256"):
            shutil.rmtree(report_dir)
            raise ValueError(
                f"sync baseline hash mismatch for {key}: expected "
                f"{project_state.get('normalized_tree_sha256')}, rebuilt {rebuilt_hash}"
            )
        merge = plan_tree_merge(
            base_normalized, target_dir, target_normalized, report_dir / "merged-tree"
        )
        (report_dir / "upstream.diff").write_text(
            render_tree_diff(base_normalized, target_normalized, "N0", "N1"),
            encoding="utf-8",
        )
        (report_dir / "local.diff").write_text(
            render_tree_diff(base_normalized, target_dir, "N0", "local"),
            encoding="utf-8",
        )
        (report_dir / "auto-merge.diff").write_text(
            render_tree_diff(target_dir, report_dir / "merged-tree", "local", "merged"),
            encoding="utf-8",
        )

    classification_counts: dict[str, int] = {}
    for entry in merge["entries"]:
        classification = entry["classification"]
        classification_counts[classification] = classification_counts.get(classification, 0) + 1
    review_category_counts = {
        "upstream-only": classification_counts.get("upstream-only", 0),
        "local-only": classification_counts.get("local-only", 0),
        "auto-merged": classification_counts.get("auto-merged", 0),
        "conflicted": len(merge["conflicts"]),
        "deleted": (
            classification_counts.get("upstream-delete", 0)
            + classification_counts.get("local-delete", 0)
        ),
        "renamed": len(merge["exact_renames"]),
    }
    plan = {
        "schema_version": 1,
        "project": key,
        "source_directory": dir_name,
        "target_path": str(target_dir.relative_to(repo_root)),
        "base_upstream_commit": base_commit,
        "target_upstream_commit": target_commit,
        "normalization_profile": profile,
        "normalizer_commit": planned_head,
        "planned_branch": planned_branch,
        "planned_head": planned_head,
        "planned_worktree_fingerprint": planned_fingerprint,
        **{key: value for key, value in merge.items() if key != "entries" and key != "conflicts"},
        "entries": merge["entries"],
        "conflicts": merge["conflicts"],
        "classification_counts": classification_counts,
        "review_category_counts": review_category_counts,
        "applied": False,
    }
    for conflict in plan["conflicts"]:
        conflict["local_source_commit"] = planned_head
        conflict["upstream_source_commit"] = target_commit
    (report_dir / "sync-plan.json").write_text(
        json.dumps(plan, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (report_dir / "conflicts.json").write_text(
        json.dumps(merge["conflicts"], indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    summary = [
        f"# ALLBOOKS sync plan for {key}", "",
        f"- Base upstream commit: `{base_commit}`",
        f"- Target upstream commit: `{target_commit}`",
        f"- Normalization profile: `{profile}`",
        f"- Local tree: `{merge['ours_tree_sha256']}`",
        f"- Conflicts: `{len(merge['conflicts'])}`", "",
        "## Required review categories", "",
    ] + [
        f"- `{name}`: {review_category_counts[name]}"
        for name in ("upstream-only", "local-only", "auto-merged", "conflicted", "deleted", "renamed")
    ] + ["", "## Detailed classification counts", ""] + [
        f"- `{name}`: {count}" for name, count in sorted(classification_counts.items())
    ]
    (report_dir / "summary.md").write_text("\n".join(summary) + "\n", encoding="utf-8")
    return plan


def apply_sync_plan(plan_path: Path, *, repo_root: Path = REPO_ROOT) -> dict:
    """Apply a conflict-free single-project plan after exact fingerprint checks."""
    plan = json.loads(plan_path.read_text(encoding="utf-8"))
    project = str(plan.get("project", ""))
    if plan.get("schema_version") != 1 or not project.startswith(("book:", "paper:")):
        raise ValueError("invalid single-project sync plan")
    if plan.get("conflicts"):
        raise ValueError("sync plan has unresolved conflicts")
    if plan.get("applied"):
        raise ValueError("sync plan is already marked applied")
    if _git_text(repo_root, "branch", "--show-current") != plan.get("planned_branch"):
        raise ValueError("current branch differs from sync plan")
    if _git_text(repo_root, "rev-parse", "HEAD") != plan.get("planned_head"):
        raise ValueError("current HEAD differs from sync plan")
    if _worktree_fingerprint(repo_root) != plan.get("planned_worktree_fingerprint"):
        raise ValueError("current worktree fingerprint differs from sync plan")
    target = (repo_root / plan["target_path"]).resolve()
    kind, name = project.split(":", 1)
    scope_root = (repo_root / "ReasBook" / ("Books" if kind == "book" else "Papers")).resolve()
    if target.parent != scope_root or target.name != name:
        raise ValueError("sync plan target escapes its exact canonical project scope")
    staged = plan_path.parent / "merged-tree"
    if tree_hash(staged) != plan.get("merged_tree_sha256"):
        raise ValueError("staged merged tree hash differs from sync plan")
    if tree_hash(target) != plan.get("ours_tree_sha256"):
        raise ValueError("current project tree differs from sync plan")
    degradation_path = repo_root / "scripts" / "state" / "degradations.json"
    degradation_before = degradation_path.read_bytes() if degradation_path.exists() else None

    def clear_project_degradation() -> None:
        if degradation_before is None:
            return
        payload = json.loads(degradation_before.decode("utf-8"))
        entries = payload.get("entries", [])
        payload["entries"] = [
            entry for entry in entries
            if not (entry.get("kind") == kind and entry.get("name") == target.name)
        ]
        temporary = degradation_path.with_suffix(".sync-tmp")
        temporary.write_text(
            json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
        )
        os.replace(temporary, degradation_path)

    try:
        apply_staged_tree(staged, target, post_apply=clear_project_degradation)
    except Exception:
        if degradation_before is not None:
            degradation_path.write_bytes(degradation_before)
        raise
    plan["applied"] = True
    plan["applied_tree_sha256"] = tree_hash(target)
    plan_path.write_text(json.dumps(plan, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return plan


# ===================================================================
# CLI
# ===================================================================
def main():
    parser = argparse.ArgumentParser(
        description="Sync files from ALLBOOKS to ReasBook"
    )
    parser.add_argument("--source", help="Path to ALLBOOKS clone")
    scope = parser.add_mutually_exclusive_group()
    scope.add_argument("--all", action="store_true", help="Preview all books")
    scope.add_argument("--book", help="Sync a specific ALLBOOKS directory")
    scope.add_argument("--paper", help="Sync one canonical paper from its ALLBOOKS project")
    parser.add_argument("--dry-run", action="store_true", help="Preview only")
    parser.add_argument(
        "--legacy-destructive-sync", action="store_true",
        help="Retired; always rejected (use the three-way planner)",
    )
    parser.add_argument("--to-commit", help="Exact ALLBOOKS target commit for a three-way plan")
    parser.add_argument("--plan", type=Path, help="Write a read-only three-way plan to this directory")
    parser.add_argument("--apply", type=Path, help="Apply an existing conflict-free sync-plan.json")
    parser.add_argument("--baseline-candidate", type=Path, help="Write an initial baseline candidate report")
    parser.add_argument("--at-commit", help="Exact ALLBOOKS commit for a baseline candidate")
    parser.add_argument("--accept-baseline", type=Path, help="Accept a reviewed baseline-candidate.json")
    parser.add_argument("--accept-sync", type=Path, help="Accept an applied sync-plan.json after full-pass")
    parser.add_argument("--automation-report", type=Path, help="Full-pass report used by --accept-sync")
    parser.add_argument("--approve-reconciliation", action="store_true")
    parser.add_argument("--reason", default="")
    parser.add_argument("--state", type=Path, default=SYNC_STATE, help="Synchronization provenance manifest")
    args = parser.parse_args()

    paper_source = None
    if args.paper:
        paper_source = next(
            (source for source, paper in PAPER_SOURCE_PROJECTS.items() if paper == args.paper), None
        )
        if paper_source is None:
            parser.error(f"no ALLBOOKS source mapping for paper:{args.paper}")

    if args.accept_baseline:
        if any((args.source, args.book, args.paper, args.all, args.apply, args.plan, args.to_commit,
                args.baseline_candidate, args.at_commit, args.accept_sync)):
            parser.error("--accept-baseline cannot be combined with planning or legacy options")
        try:
            accepted = accept_baseline_candidate(
                args.accept_baseline, args.state, reason=args.reason,
                approve_reconciliation=args.approve_reconciliation,
            )
        except (OSError, ValueError, json.JSONDecodeError) as error:
            parser.error(str(error))
        print(f"Accepted initial sync baseline {accepted['accepted_upstream_commit']}")
        return

    if args.accept_sync:
        if not args.automation_report:
            parser.error("--accept-sync requires --automation-report")
        try:
            accepted = accept_verified_sync(args.accept_sync, args.automation_report, args.state)
        except (OSError, ValueError, json.JSONDecodeError) as error:
            parser.error(str(error))
        print(f"Accepted verified upstream commit {accepted['accepted_upstream_commit']}")
        return

    if args.apply:
        if any((args.source, args.book, args.paper, args.all, args.dry_run, args.legacy_destructive_sync,
                args.to_commit, args.plan)):
            parser.error("--apply cannot be combined with source, scope, plan, or legacy options")
        try:
            applied = apply_sync_plan(args.apply)
        except (OSError, ValueError, json.JSONDecodeError) as error:
            parser.error(str(error))
        print(f"Applied conflict-free sync plan for {applied['project']}")
        return

    if not args.source or not (args.book or args.paper or args.all):
        parser.error("--source and exactly one of --book/--paper/--all are required")

    source = Path(args.source)
    if not source.exists():
        print(f"ERROR: Source not found: {source}", file=sys.stderr)
        sys.exit(1)

    if args.baseline_candidate:
        if args.all or not (args.book or args.paper) or not args.at_commit:
            parser.error("--baseline-candidate requires one --book/--paper and --at-commit")
        try:
            candidate = create_baseline_candidate(
                source_repo=source, dir_name=args.book or paper_source,
                at_commit=args.at_commit, report_dir=args.baseline_candidate,
                kind="paper" if args.paper else "book", project_name=args.paper,
            )
        except (OSError, ValueError, json.JSONDecodeError) as error:
            parser.error(str(error))
        print(
            f"Baseline candidate {candidate['project']}: "
            f"exact_match={candidate['exact_match']}; report={args.baseline_candidate}"
        )
        return
    if args.at_commit:
        parser.error("--at-commit requires --baseline-candidate")

    if args.plan:
        if args.all or not (args.book or args.paper) or not args.to_commit:
            parser.error("--plan requires one --book/--paper and --to-commit; --all is read-only inventory only")
        if args.dry_run or args.legacy_destructive_sync:
            parser.error("--plan cannot be combined with legacy or dry-run mode")
        try:
            plan = create_sync_plan(
                source_repo=source, dir_name=args.book or paper_source,
                to_commit=args.to_commit, report_dir=args.plan, state_path=args.state,
                kind="paper" if args.paper else "book", project_name=args.paper,
            )
        except (OSError, ValueError, json.JSONDecodeError) as error:
            parser.error(str(error))
        print(
            f"Planned {plan['project']}: {len(plan['conflicts'])} conflict(s); "
            f"report={args.plan}"
        )
        return
    if args.to_commit:
        parser.error("--to-commit requires --plan")

    destination_exists = False
    if args.book:
        if args.book in PAPER_SOURCE_PROJECTS:
            parser.error(f"{args.book} is a canonical paper source; use --paper")
        destination_exists = (BOOKS_DIR / DIR_MAP.get(args.book, args.book)).exists()
    elif args.paper:
        destination_exists = (PAPERS_DIR / args.paper).exists()
    mode_error = _legacy_mode_error(
        dry_run=args.dry_run,
        legacy_destructive_sync=args.legacy_destructive_sync,
        all_books=args.all,
        destination_exists=destination_exists,
    )
    if mode_error:
        parser.error(mode_error)

    if args.book:
        sync_book(source, args.book, args.dry_run)
    elif args.paper:
        if not args.dry_run:
            parser.error("paper mutation requires --baseline-candidate or --plan/--apply")
        preview_paper(source, paper_source, args.paper)
    elif args.all:
        for d in sorted(source.iterdir()):
            if d.is_dir() and any(d.rglob("*.lean")):
                paper_name = PAPER_SOURCE_PROJECTS.get(d.name)
                if paper_name:
                    preview_paper(source, d.name, paper_name)
                else:
                    sync_book(source, d.name, args.dry_run)


if __name__ == "__main__":
    main()
