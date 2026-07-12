"""
Inventory and validation module for the ReasBook normalization system.

Reads the original file inventory from ``docs/inventory-1a2c1941-full-statement-list.md``
and/or directly from git, and provides functions to verify content preservation
after normalization (merging per-statement files into section files).
"""

import re
import subprocess
from pathlib import Path
from typing import Optional

from .section_map import BOOK_CONFIGS, get_config

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
INVENTORY_PATH = REPO_ROOT / "docs" / "inventory-1a2c1941-full-statement-list.md"


# ──────────────────────────────────────────────────────────────────────────────
# Inventory file parsing
# ──────────────────────────────────────────────────────────────────────────────


def read_inventory_from_file() -> dict[str, list[str]]:
    """Parse the inventory markdown file.

    Returns:
        dict mapping ``book_name`` (the name as it appears in the inventory
        heading, e.g. ``"AlgebraicTopology_May_1999"``) to a list of relative
        file paths within that book.  The paths are relative to the book root
        and include the ``.lean`` extension.

        For older per-statement books with ``### ``ChapXX/`` `` subheadings,
        files appear exactly as listed (e.g. ``Chap01/Definition_1_1_1.lean``).

        For canonical books (those already in ``Chapters/`` layout), section
        files are included (e.g. ``Chapters/Chap01.lean``,
        ``Chapters/Chap01/section01.lean``).

        For papers, files are listed directly under the ``## Paper: ...`` heading
        without intermediate ``###`` subheadings.

    Parsing strategy
    ----------------
    The inventory file has sections delimited by ``## Book: <name>`` or
    ``## Paper: <name>`` headings, separated by ``---`` horizontal rules.
    Within each section, ``### ``...`` `` subheadings indicate chapter/section
    directories, and ``- ``...`` `` list items show the files.  Canonical books
    and papers may have no ``###`` subheadings at all — in those cases all
    ``- ``...`` `` list items under the ``##`` heading are collected directly.
    """
    text = INVENTORY_PATH.read_text(encoding="utf-8")

    # ── Phase 1: Split into per-book/per-paper sections ───────────────────────
    # Match headings like "## Book: AlgebraicTopology_May_1999" or
    # "## Paper: SmoothMinimization_Nesterov_2004".
    section_pattern = re.compile(r"^## (Book|Paper): (.+)$", re.MULTILINE)
    matches = list(section_pattern.finditer(text))

    result: dict[str, list[str]] = {}
    for i, m in enumerate(matches):
        name = m.group(2).strip()
        # The section body runs from the end of this heading to the start of
        # the next heading (or EOF).
        start = m.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        body = text[start:end]

        files = _extract_files_from_book_body(body)
        result[name] = files

    return result


def _extract_files_from_book_body(body: str) -> list[str]:
    """Parse the body of a single Book/Paper section from the inventory.

    The body may contain ``### ``...`` `` subheadings for older per-statement
    books, or may be flat (canonical books and papers).  In both cases
    ``- ``...`` `` list items signal ``.lean`` file paths.

    Args:
        body: The raw text between two ``## …`` headings (or between the last
            heading and EOF).

    Returns:
        List of ``.lean`` file paths relative to the book root.
    """
    # ── Strategy: collect every ``- ``...`` `` line whose backtick content
    #     looks like a .lean file path.  These lines are unambiguous because
    #     all other list items in the inventory are not backtick-quoted paths.
    file_pattern = re.compile(r"^- `([^`]+\.lean)`\s*$", re.MULTILINE)
    return file_pattern.findall(body)


# ──────────────────────────────────────────────────────────────────────────────
# Git-based inventory
# ──────────────────────────────────────────────────────────────────────────────


def read_inventory_from_git(commit: str = "1a2c1941") -> dict[str, list[str]]:
    """Read file inventory directly from git at a given commit.

    Uses ``git ls-tree -r --name-only`` to list every ``.lean`` file under
    ``ReasBook/Books/``.  The results are grouped by the original book
    directory name (the first component under ``Books/``).

    Args:
        commit: The git commit hash or ref to query.  Default ``"1a2c1941"``.

    Returns:
        dict mapping ``original_book_name`` (the directory name as it existed
        at that commit, e.g. ``"MayConciseRevised"``) to a list of relative
        file paths within that book (e.g. ``"Basic.lean"``,
        ``"Chap01/Definition_1_1_1.lean"``).
    """
    proc = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", commit, "ReasBook/Books/"],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"git ls-tree failed for commit {commit}: {proc.stderr.strip()}"
        )

    # Lines look like: ReasBook/Books/MayConciseRevised/Chap01/Definition_1_1_1.lean
    result: dict[str, list[str]] = {}
    prefix = "ReasBook/Books/"

    for line in proc.stdout.strip().split("\n"):
        line = line.strip()
        if not line or not line.endswith(".lean"):
            continue
        if not line.startswith(prefix):
            continue

        # Strip the common prefix to get: <book_name>/<rest>
        relative = line[len(prefix):]
        parts = relative.split("/", 1)
        book_name = parts[0]
        file_path = parts[1] if len(parts) > 1 else ""

        result.setdefault(book_name, []).append(file_path)

    return result


# ──────────────────────────────────────────────────────────────────────────────
# Expected file counts
# ──────────────────────────────────────────────────────────────────────────────


def get_expected_file_count(book_name: str, config: dict) -> int:
    """Calculate the expected number of ``.lean`` files after normalization.

    The logic depends on the book type:

    - **canonical / library / empty**: no structural changes; the count is the
      same as the number of original files listed in the inventory.

    - **three_level / two_level / section_subdir / roman / flat_chapter**:
      per-statement files are merged into section files.  This function
      computes the number of resulting section files based on the book's
      structure and ``max_lines`` limit, but because the exact number depends
      on file sizes, it returns a **minimum** estimate (one section file per
      unique chapter-section pair).  Root files (Book.lean, Basic.lean) are
      added to the count.

    Args:
        book_name: The new (normalized) book name as it appears in the
            inventory headings.
        config: The book configuration dict from ``section_map.BOOK_CONFIGS``
            (keyed by original name).  Used to identify the book type and
            root files.

    Returns:
        Estimated minimum number of ``.lean`` files after normalization.
        Returns the original file count for books that are not restructured.
    """
    book_type = config.get("type", "canonical")

    if book_type in ("canonical", "library", "empty"):
        # These books are not restructured; the file count stays the same.
        inventory = read_inventory_from_file()
        return len(inventory.get(book_name, []))

    # For structured books (three_level, two_level, roman, section_subdir,
    # flat_chapter), compute a rough estimate from the inventory.
    inventory = read_inventory_from_file()
    files = inventory.get(book_name, [])
    if not files:
        return 0

    root_files = config.get("root_files", [])
    root_count = len(root_files)

    # ── Collect unique (chapter, section) pairs from per-statement files ──────
    # Per-statement files have names like:
    #   Chap01/Definition_1_1_1.lean  (three_level)
    #   Items/Chap01/Definition_1_1.lean  (two_level)
    #   Chap01/Sec01_02/Definition_2_1_1.lean  (section_subdir)

    chapter_sections: set[tuple[int, int]] = set()

    for f in files:
        cs = _extract_chapter_section(f, config)
        if cs is not None:
            chapter_sections.add(cs)

    # Minimum: one section file per unique (chapter, section).
    # In practice there may be more due to max_lines splitting, but this is a
    # sanity-check floor.
    section_count = len(chapter_sections)

    # Add the Book.lean per chapter (if present in root_files).
    # Some books also have one chapter-level file per chapter (e.g.
    # Chap01.lean), but that varies.  We only count root_files.
    return root_count + section_count


def _extract_chapter_section(
    file_path: str, config: dict
) -> Optional[tuple[int, int]]:
    """Extract the (chapter, section) pair from a per-statement file path.

    Handles the naming scheme declared in the book config:

    - **three_level**: ``Chap02/Definition_2_3_1.lean`` → chapter=2, section=3.
    - **two_level**: ``Items/Chap01/Definition_1_17.lean`` → chapter=1,
      section is derived by dividing the item number by ``items_per_section``.
    - **section_subdir**: ``Chap01/Sec01_02/Definition_1_2_1.lean`` →
      chapter=1, section=2.

    Args:
        file_path: Relative path within the book, e.g. ``"Chap01/Definition_1_1_1.lean"``.
        config: The book configuration dict.

    Returns:
        ``(chapter_num, section_num)`` if a chapter-section pair can be
        determined, or ``None`` if the path is a root file or cannot be parsed.
    """
    naming = config.get("naming")
    stem = Path(file_path).stem  # e.g. "Definition_1_1_1"

    if naming == "three_level":
        # Match patterns like "Definition_1_2_3", "Lemma_10_5_1", etc.
        m = re.match(
            r"[A-Za-z]+_(\d+)_(\d+)_\d+", stem
        )
        if m:
            return (int(m.group(1)), int(m.group(2)))

    elif naming == "two_level":
        # Patterns like "Definition_1_17" → chapter=1, item=17.
        m = re.match(r"[A-Za-z]+_(\d+)_(\d+)", stem)
        if m:
            chapter = int(m.group(1))
            item = int(m.group(2))
            items_per_section = config.get("items_per_section", 20)
            section = (item - 1) // items_per_section + 1
            return (chapter, section)

    elif naming == "section_subdir":
        # Path: Chap01/Sec01_02/Definition_1_2_1.lean
        # Extract section from the SecXX_YY directory name.
        sec_m = re.search(r"/Sec(\d+)_(\d+)/", file_path)
        if sec_m:
            return (int(sec_m.group(1)), int(sec_m.group(2)))

    return None


# ──────────────────────────────────────────────────────────────────────────────
# Statement marker extraction
# ──────────────────────────────────────────────────────────────────────────────


# Pattern for ``/-! ### <Name> -/`` markers inserted by merge_section_group.
_MARKER_RE = re.compile(r"/-!\s*###\s+(.+?)\s*-/", re.MULTILINE)


def count_statement_markers(content: str) -> list[str]:
    """Extract all ``/-! ### <name> -/`` markers from merged content.

    These markers are inserted by
    :func:`~.merger.merge_section_group` and serve as anchors
    for verifying that every original per-statement file is represented in the
    merged output.

    Args:
        content: The full text of a merged ``.lean`` file (or concatenation of
            several merged files).

    Returns:
        List of marker names (e.g. ``['Definition_1_1_1', 'Lemma_1_2_5']``)
        in the order they appear.
    """
    return _MARKER_RE.findall(content)


# ──────────────────────────────────────────────────────────────────────────────
# Content preservation verification
# ──────────────────────────────────────────────────────────────────────────────


def verify_content_preservation(
    original_files: list[str],
    merged_content: str,
) -> tuple[list[str], list[str]]:
    """Check that all original statement names appear in merged content.

    Compares the statement names derived from the original per-statement
    filenames against the ``/-! ### <name> -/`` markers found in the merged
    output.

    Args:
        original_files: List of original per-statement ``.lean`` file paths
            relative to the book root (e.g. ``["Chap01/Definition_1_1_1.lean",
            "Chap01/Lemma_1_2_5.lean"]``).
        merged_content: The full text of one or more merged section files
            concatenated together.

    Returns:
        ``(found, missing)`` — two lists of statement names.

            - **found**: statement names derived from original filenames that
              have a matching ``/-! ### ... -/`` marker in the merged content.
            - **missing**: original filenames whose statement name has NO
              corresponding marker.  An empty ``missing`` list means full
              preservation.
    """
    # Extract statement names from original filenames.
    # e.g. "Chap01/Definition_1_1_1.lean" → "Definition_1_1_1"
    original_names: set[str] = set()
    for f in original_files:
        stem = Path(f).stem
        if stem and not stem.startswith("."):
            original_names.add(stem)

    # Extract markers from merged content.
    markers = set(_MARKER_RE.findall(merged_content))

    found = sorted(original_names & markers)
    missing = sorted(original_names - markers)

    return found, missing


# ──────────────────────────────────────────────────────────────────────────────
# Full-book verification
# ──────────────────────────────────────────────────────────────────────────────


def verify_book(
    book_name: str,
    merged_dir: Path,
) -> dict[str, tuple[list[str], list[str]]]:
    """Run content-preservation verification for every merged section file
    of a book.

    For each merged ``.lean`` file in *merged_dir*, this function looks up
    the original per-statement files that should have been merged into that
    section (from the inventory) and checks that all of their statement names
    appear as ``/-! ### ... -/`` markers in the merged content.

    Args:
        book_name: The new (normalized) book name as it appears in the
            inventory headings.
        merged_dir: Absolute path to the directory containing the merged
            ``.lean`` output files (e.g. the book's ``Chapters/``
            subdirectory).

    Returns:
        A dict mapping merged section filenames (e.g. ``"section01.lean"``)
        to ``(found, missing)`` tuples, where *found* and *missing* are
        the lists returned by :func:`verify_content_preservation`.  An empty
        dict means no merged files were found under *merged_dir*.

        Sections whose *missing* list is non-empty indicate a content
        preservation gap.
    """
    merged_dir = Path(merged_dir)
    if not merged_dir.is_dir():
        return {}

    # Build a set of merged filenames (we do not recurse into chapter
    # subdirectories on purpose — we verify at the section file level).
    merged_files = sorted(merged_dir.glob("*.lean"))
    if not merged_files:
        return {}

    # Read inventory for this book.
    inventory = read_inventory_from_file()
    original_files = inventory.get(book_name, [])
    if not original_files:
        return {}

    # Group original files by the section they would belong to.
    # This mapping depends on the book type, so we need the config.
    config = get_config_by_new_name(book_name)
    if config is None:
        # Fall back: verify against all original files at once.
        all_merged = "\n".join(
            mf.read_text(encoding="utf-8") for mf in merged_files
        )
        found, missing = verify_content_preservation(original_files, all_merged)
        return {"__all__": (found, missing)}

    # For three_level books, group original files by (chapter, section).
    section_groups: dict[str, list[str]] = {}
    for f in original_files:
        cs = _extract_chapter_section(f, config)
        if cs is not None:
            chap, sec = cs
            section_label = f"section{sec:02d}"
            section_groups.setdefault(section_label, []).append(f)

    result: dict[str, tuple[list[str], list[str]]] = {}

    for mf in merged_files:
        mf_stem = mf.stem  # e.g. "section01" or "section01_part2"
        # Match to the base section name.
        base = re.match(r"(section\d+)(?:_part\d+)?$", mf_stem)
        if base is None:
            continue
        section_label = base.group(1)
        orig = section_groups.get(f"{section_label}", [])
        content = mf.read_text(encoding="utf-8")
        found, missing = verify_content_preservation(orig, content)
        result[mf.name] = (found, missing)

    return result


def get_config_by_new_name(new_name: str) -> Optional[dict]:
    """Look up a book configuration by its normalized (new) name.

    Args:
        new_name: The normalized book name, e.g.
            ``"AlgebraicTopology_May_1999"``.

    Returns:
        The config dict from ``section_map.BOOK_CONFIGS`` if found, or
        ``None``.
    """
    for cfg in BOOK_CONFIGS.values():
        if cfg["new_name"] == new_name:
            return cfg
    return None
