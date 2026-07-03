#!/usr/bin/env python3
"""
merge_statements.py — Merge per-statement .lean files into per-section .lean files.

Reads a book directory containing per-statement files (e.g. Definition_1_4_1.lean,
Theorem_2_6_1.lean) and merges them into section-level files under Chapters/ChapNN/.

Usage:
    python3 scripts/merge_statements.py Books/BookName              # real run
    python3 scripts/merge_statements.py Books/BookName --dry-run    # preview only
    python3 scripts/merge_statements.py Books/BookName --max-lines 1800
    python3 scripts/merge_statements.py Books/BookName --section-map section_map.json
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


# ─── constants ───────────────────────────────────────────────────────────────

DEFAULT_MAX_LINES = 1500
SECTION_FILE_PATTERN = re.compile(r"^section(\d+)(?:_part(\d+))?\.lean$")
CHAPTER_DIR_PATTERN = re.compile(r"^chap(\d+)$", re.IGNORECASE)
ROMAN_TO_INT = {"i": 1, "ii": 2, "iii": 3, "iv": 4, "v": 5, "vi": 6, "vii": 7,
                "viii": 8, "ix": 9, "x": 10, "xi": 11, "xii": 12, "xiii": 13}

# Files that match these patterns are per-statement, not section-level
STATEMENT_NAME_RE = re.compile(
    r"^(Definition|Theorem|Lemma|Corollary|Example|Proposition|Remark|Exercise|"
    r"Construction|Method|Principle|Program|ProofStep|Problem|Infra|Recall|"
    r"Text|Note|Conjecture|Assumption|Fact)_",
    re.IGNORECASE,
)

# Comment line that separates import header from code body
DECLARATION_MARKER = "-- Declarations for this item"


# ─── data structures ─────────────────────────────────────────────────────────

@dataclass
class StmtFile:
    """A single per-statement .lean file."""
    path: Path
    chapter: int
    section: int        # 0 if unknown (two-level naming)
    item: int           # item number within chapter
    chapter_dir: str    # e.g. "Chap01" or "Items/Chap01"
    is_items: bool      # True if under Items/ directory

    @property
    def module_name(self) -> str:
        return self.path.stem


@dataclass
class SectionGroup:
    """A group of StmtFile objects belonging to the same (chapter, section)."""
    chapter: int
    section: int
    files: list[StmtFile] = field(default_factory=list)

    @property
    def total_lines(self) -> int:
        return sum(_count_code_lines(f.path) for f in self.files)


@dataclass
class ImportInfo:
    """Collected imports from a group of files."""
    mathlib_imports: list[str] = field(default_factory=list)
    cross_imports: list[str] = field(default_factory=list)  # to be removed after merge


# ─── helpers ─────────────────────────────────────────────────────────────────

def _count_code_lines(path: Path) -> int:
    """Count non-empty, non-comment lines in a .lean file."""
    count = 0
    try:
        with open(path) as f:
            for line in f:
                stripped = line.strip()
                if stripped and not stripped.startswith("--"):
                    count += 1
    except Exception:
        pass
    return count


def _read_file_body(path: Path) -> str:
    """Read a .lean file and return only the code body (after the declaration marker)."""
    try:
        content = path.read_text(encoding="utf-8")
    except Exception:
        return ""
    idx = content.find(DECLARATION_MARKER)
    if idx >= 0:
        # Find the next newline after the marker
        nl = content.find("\n", idx)
        if nl >= 0:
            return content[nl + 1:]
    # Fallback: if no marker found, strip common import headers
    lines = content.splitlines()
    body_start = 0
    for i, line in enumerate(lines):
        if line.startswith("import "):
            body_start = i + 1
            continue
        if line.strip() == "":
            continue
        if line.startswith("--"):
            continue
        body_start = i
        break
    return "\n".join(lines[body_start:])


def _read_imports(path: Path) -> list[str]:
    """Extract import lines from a .lean file."""
    imports = []
    try:
        with open(path) as f:
            for line in f:
                stripped = line.strip()
                if stripped.startswith("import "):
                    imports.append(stripped)
                elif stripped and not stripped.startswith("--"):
                    break
    except Exception:
        pass
    return imports


# ─── file discovery & classification ─────────────────────────────────────────

def discover_book_files(book_dir: Path) -> tuple[list[StmtFile], dict[int, list[Path]]]:
    """
    Scan a book directory and return:
      - list of per-statement StmtFile objects (chapter from filename, not directory)
      - dict of existing section files: {chapter_num: [path, ...]}
    """
    stmt_files: list[StmtFile] = []
    existing_sections: dict[int, list[Path]] = defaultdict(list)

    for lean_file in sorted(book_dir.rglob("*.lean")):
        rel = lean_file.relative_to(book_dir)
        parts = rel.parts

        # Check for existing section files under Chapters/ChapNN/
        if parts[0].lower() == "chapters" and len(parts) >= 3:
            m = CHAPTER_DIR_PATTERN.match(parts[1])
            if m:
                chap_num = int(m.group(1))
                sf_match = SECTION_FILE_PATTERN.match(parts[2])
                if sf_match:
                    existing_sections[chap_num].append(lean_file)
                    continue

        # Check if this looks like a per-statement file
        filename = lean_file.stem
        if not STATEMENT_NAME_RE.match(filename):
            continue

        chap, sec, item = _parse_stmt_filename(filename)
        if chap == 0:
            continue

        # Determine if this file lives under an Items/ directory
        is_items = "items" in [p.lower() for p in parts]

        # Determine the source directory for reporting
        source_dir = str(Path(*parts[:-1])) if len(parts) > 1 else "."

        stmt_files.append(StmtFile(
            path=lean_file,
            chapter=chap,
            section=sec,
            item=item,
            chapter_dir=source_dir,
            is_items=is_items,
        ))

    return stmt_files, dict(existing_sections)


def _parse_stmt_filename(name: str) -> tuple[int, int, int]:
    """
    Parse a statement filename into (chapter_num, section_num, item_num).

    Three-level: Definition_2_6_1 → (2, 6, 1)
    Two-level:   Definition_1_17  → (1, 0, 17)  (section unknown)
    Section-0:   Corollary_2_0_4 → (2, 0, 4)   (section 0 is valid)
    """
    # Remove the type prefix
    m = STATEMENT_NAME_RE.match(name)
    if not m:
        return 0, 0, 0
    rest = name[m.end():]

    parts = rest.split("_")
    nums = []
    for p in parts:
        try:
            nums.append(int(p))
        except ValueError:
            pass

    if len(nums) >= 3:
        # Three-level: chapter_section_item (or chapter_section_item_extra)
        return nums[0], nums[1], nums[2]
    elif len(nums) == 2:
        # Two-level: chapter_item
        return nums[0], 0, nums[1]
    elif len(nums) == 1:
        return nums[0], 0, 0
    return 0, 0, 0


# ─── merge logic ─────────────────────────────────────────────────────────────

def group_by_section(stmt_files: list[StmtFile]) -> dict[tuple[int, int], list[StmtFile]]:
    """Group statement files by (chapter, section), sorted by item number."""
    groups: dict[tuple[int, int], list[StmtFile]] = defaultdict(list)
    for sf in stmt_files:
        key = (sf.chapter, sf.section)
        groups[key].append(sf)

    for key in groups:
        groups[key].sort(key=lambda sf: (sf.item, sf.module_name))

    return dict(groups)


def _classify_import(imp: str, book_module_prefix: str) -> tuple[str, bool]:
    """
    Classify an import line.
    Returns (import_line, is_cross_import).
    Cross-import = imports something from within the same book's per-statement tree.
    """
    stripped = imp.strip()
    if not stripped.startswith("import "):
        return stripped, False

    module = stripped[len("import "):].strip()
    # Check if this imports from within the same book
    if module.startswith(book_module_prefix):
        # It's an internal import — will be resolved by merging
        return stripped, True

    return stripped, False


def merge_group(group: list[StmtFile], book_module_prefix: str,
                max_lines: int) -> list[tuple[str, str]]:
    """
    Merge a list of StmtFile objects into one or more section files.
    Returns list of (filename, content) pairs.
    """
    # Collect all imports and code bodies
    all_mathlib_imports: list[str] = []
    all_bodies: list[str] = []
    total_lines = 0

    for sf in group:
        imports = _read_imports(sf.path)
        for imp in imports:
            _, is_cross = _classify_import(imp, book_module_prefix)
            if not is_cross:
                if imp not in all_mathlib_imports:
                    all_mathlib_imports.append(imp)

        body = _read_file_body(sf.path)
        if body.strip():
            # Add a comment header showing the source
            src_note = f"\n/-! ### {sf.module_name} (from {sf.chapter_dir}) -/\n"
            all_bodies.append(src_note + body.strip())
            total_lines += body.count("\n") + 3  # rough count

    if not all_bodies:
        return []

    imports_block = "\n".join(sorted(set(all_mathlib_imports)))
    merged_content = "\n".join(all_bodies)
    full_content = f"{imports_block}\n\n{DECLARATION_MARKER} will be appended below by the statement pipeline.\n\n{merged_content}\n"

    # Decide whether to split
    if total_lines <= max_lines:
        return [(f"section{group[0].section:02d}.lean", full_content)]

    # Need to split: distribute bodies across parts
    parts = []
    current_part_lines = 0
    current_part_bodies: list[str] = []
    part_num = 1

    for body in all_bodies:
        body_lines = body.count("\n") + 1
        if current_part_lines + body_lines > max_lines and current_part_bodies:
            # Emit current part
            part_content = f"{imports_block}\n\n{DECLARATION_MARKER} will be appended below by the statement pipeline.\n\n" + "\n".join(current_part_bodies) + "\n"
            parts.append((f"section{group[0].section:02d}_part{part_num}.lean", part_content))
            part_num += 1
            current_part_bodies = [body]
            current_part_lines = body_lines
        else:
            current_part_bodies.append(body)
            current_part_lines += body_lines

    if current_part_bodies:
        part_content = f"{imports_block}\n\n{DECLARATION_MARKER} will be appended below by the statement pipeline.\n\n" + "\n".join(current_part_bodies) + "\n"
        parts.append((f"section{group[0].section:02d}_part{part_num}.lean", part_content))

    return parts


def generate_chapter_aggregator(chapter: int, section_files: list[str]) -> str:
    """Generate a ChapNN.lean aggregator that imports all section files."""
    imports = [f"import {sf.replace('.lean', '').replace('/', '.')}" for sf in section_files]
    return "\n".join(sorted(imports)) + "\n"


# ─── main entry point ────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Merge per-statement .lean files into per-section .lean files"
    )
    parser.add_argument(
        "book_dir",
        help="Path to the book directory (e.g. Books/ConvexAnalysis_Rockafellar_1970)",
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="Preview changes without writing any files",
    )
    parser.add_argument(
        "--max-lines", type=int, default=DEFAULT_MAX_LINES,
        help=f"Maximum lines per section file before splitting (default: {DEFAULT_MAX_LINES})",
    )
    parser.add_argument(
        "--section-map",
        help="JSON file mapping (chapter, item_range) → section for two-level naming books",
    )
    parser.add_argument(
        "--json-section-template",
        help="Output a JSON template for --section-map (use with --dry-run)",
    )
    parser.add_argument(
        "--book-module",
        help="Book module prefix for import classification (auto-detected if omitted)",
    )
    args = parser.parse_args()

    book_dir = Path(args.book_dir).resolve()
    if not book_dir.is_dir():
        print(f"Error: {book_dir} is not a directory", file=sys.stderr)
        sys.exit(1)

    book_name = book_dir.name

    # Auto-detect book module prefix
    book_module_prefix = args.book_module or book_name

    # Load section map for two-level naming
    section_map: dict[int, dict[int, int]] = {}  # chapter -> {item -> section}
    if args.section_map:
        with open(args.section_map) as f:
            raw = json.load(f)
        for ch_str, ranges in raw.items():
            ch = int(ch_str)
            section_map[ch] = {}
            for r in ranges:
                sec = r["section"]
                for item in range(r["from"], r["to"] + 1):
                    section_map[ch][item] = sec

    # Discover files
    stmt_files, existing_sections = discover_book_files(book_dir)

    if not stmt_files:
        print(f"No per-statement files found in {book_dir}")
        sys.exit(0)

    # ─── JSON section template ───────────────────────────────────────────

    if args.json_section_template:
        template: dict[str, list[dict]] = {}
        for sf in stmt_files:
            rest = STATEMENT_NAME_RE.sub("", sf.path.stem)
            num_parts = len([p for p in rest.split("_") if p.lstrip("-").isdigit()])
            if num_parts == 2 and sf.section == 0:
                ch = str(sf.chapter)
                if ch not in template:
                    template[ch] = []

        if template:
            for ch_str in sorted(template, key=int):
                ch = int(ch_str)
                ch_files = sorted(
                    [sf for sf in stmt_files
                     if sf.chapter == ch and sf.section == 0],
                    key=lambda sf: sf.item,
                )
                if ch_files:
                    min_item = ch_files[0].item
                    max_item = ch_files[-1].item
                    ranges = []
                    start = min_item
                    while start <= max_item:
                        end = min(start + 14, max_item)
                        ranges.append({"section": len(ranges) + 1, "from": start, "to": end})
                        start = end + 1
                    template[ch_str] = ranges
            print(json.dumps(template, indent=2))
        else:
            print("{}")
        sys.exit(0)

    # Apply section map for two-level naming books
    # Three-level naming already has section from filename; section=0 there is valid.
    # Two-level naming: section=0 means unknown → need section_map or use item as proxy.
    unassigned = 0
    for sf in stmt_files:
        # Determine if this is two-level naming: does the filename have exactly 2 numbers?
        rest = STATEMENT_NAME_RE.sub("", sf.path.stem)
        num_parts = len([p for p in rest.split("_") if p.lstrip("-").isdigit()])
        is_two_level = (num_parts == 2)

        if is_two_level and sf.section == 0:
            if sf.chapter in section_map and sf.item in section_map[sf.chapter]:
                sf.section = section_map[sf.chapter][sf.item]
            else:
                # Without a section map, use item number as a proxy
                sf.section = sf.item
                unassigned += 1

    if unassigned > 0:
        print(f"Warning: {unassigned} files have no section mapping. "
              f"Using item number as section proxy. Consider providing --section-map.",
              file=sys.stderr)

    # Group by (chapter, section)
    groups = group_by_section(stmt_files)

    # Prepare output
    chapters_dir = book_dir / "Chapters"
    plan: list[dict] = []  # dry-run report

    for (chapter, section), group in sorted(groups.items()):
        chap_dir = chapters_dir / f"Chap{chapter:02d}"
        merged = merge_group(group, book_module_prefix, args.max_lines)

        for filename, content in merged:
            output_path = chap_dir / filename
            rel_path = output_path.relative_to(book_dir)
            plan.append({
                "chapter": chapter,
                "section": section,
                "file": str(rel_path),
                "lines": content.count("\n"),
                "source_files": [str(f.path.relative_to(book_dir)) for f in group],
                "content": content,
            })

    # Generate chapter aggregators
    chap_to_sections: dict[int, list[str]] = defaultdict(list)
    for entry in plan:
        chap_to_sections[entry["chapter"]].append(
            f"Chapters/Chap{entry['chapter']:02d}/{Path(entry['file']).name}"
        )

    # ─── JSON section template ───────────────────────────────────────────────

    if args.json_section_template:
        # Generate a template mapping for two-level naming books
        template: dict[str, list[dict]] = {}
        for sf in stmt_files:
            rest = STATEMENT_NAME_RE.sub("", sf.path.stem)
            num_parts = len([p for p in rest.split("_") if p.lstrip("-").isdigit()])
            if num_parts == 2 and sf.section == 0:
                ch = str(sf.chapter)
                if ch not in template:
                    template[ch] = []
        if template:
            # Suggest reasonable section boundaries
            for ch_str in sorted(template, key=int):
                ch = int(ch_str)
                ch_files = sorted(
                    [sf for sf in stmt_files
                     if sf.chapter == ch and sf.section == 0],
                    key=lambda sf: sf.item,
                )
                if ch_files:
                    min_item = ch_files[0].item
                    max_item = ch_files[-1].item
                    # Heuristic: group by ranges of ~15 items
                    ranges = []
                    start = min_item
                    while start <= max_item:
                        end = min(start + 14, max_item)
                        ranges.append({"section": len(ranges) + 1, "from": start, "to": end})
                        start = end + 1
                    template[ch_str] = ranges
            print(json.dumps(template, indent=2))
        else:
            print("{}  # No two-level naming files found")
        sys.exit(0)

    # ─── output ───────────────────────────────────────────────────────────

    if args.dry_run:
        print(f"\n{'='*60}")
        print(f"DRY RUN: {book_name}")
        print(f"{'='*60}")
        print(f"Per-statement files found: {len(stmt_files)}")
        print(f"Section groups: {len(groups)}")
        print(f"Output files: {len(plan)}")

        for chapter in sorted(chap_to_sections):
            sections = chap_to_sections[chapter]
            print(f"\n  Chapter {chapter:02d} ({len(sections)} section files):")
            for sf in sorted(sections):
                print(f"    {sf}")

        print(f"\n  Chapters/ChapNN.lean aggregators: {len(chap_to_sections)}")
        print(f"\n  Files to DELETE after merge: {len(stmt_files)}")

        # Sample content preview (first section of first chapter)
        if plan:
            first = plan[0]
            print(f"\n{'─'*60}")
            print(f"Preview: {first['file']} ({first['lines']} lines)")
            print(f"Sources: {len(first['source_files'])} files")
            print(f"{'─'*60}")
            preview_lines = first["content"].splitlines()[:30]
            print("\n".join(preview_lines))
            if first["content"].count("\n") > 30:
                print("... (truncated)")

        sys.exit(0)

    # ─── real run ─────────────────────────────────────────────────────────

    print(f"Merging {len(stmt_files)} per-statement files into {len(plan)} section files...")

    # Ensure Chapters/ directory exists
    chapters_dir.mkdir(parents=True, exist_ok=True)

    # Write section files
    for entry in plan:
        output_path = book_dir / entry["file"]
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(entry["content"], encoding="utf-8")
        print(f"  Wrote {entry['file']} ({entry['lines']} lines, {len(entry['source_files'])} sources)")

    # Write chapter aggregators
    for chapter, section_files in sorted(chap_to_sections.items()):
        agg_path = chapters_dir / f"Chap{chapter:02d}.lean"
        agg_content = generate_chapter_aggregator(chapter, section_files)
        agg_path.write_text(agg_content, encoding="utf-8")
        print(f"  Wrote Chapters/Chap{chapter:02d}.lean ({len(section_files)} sections)")

    # Print deletion commands
    print(f"\n{'='*60}")
    print(f"Merge complete. Next steps:")
    print(f"{'='*60}")
    print(f"\n1. Review the generated section files under {chapters_dir}")
    print(f"\n2. Delete per-statement source files:")
    sources_by_dir: dict[str, list[str]] = defaultdict(list)
    for sf in stmt_files:
        rel = str(sf.path.relative_to(book_dir))
        parent = str(Path(rel).parent)
        sources_by_dir[parent].append(sf.path.name)

    for parent_dir in sorted(sources_by_dir):
        files = sources_by_dir[parent_dir]
        if len(files) <= 5:
            for f in sorted(files):
                print(f"   git rm {book_dir / parent_dir / f}")
        else:
            print(f"   # {len(files)} files in {parent_dir}/ (batch delete)")
            # Group by prefix for efficiency
            by_prefix: dict[str, list[str]] = defaultdict(list)
            for f in sorted(files):
                prefix = f.split("_")[0] if "_" in f else f
                by_prefix[prefix].append(f)
            for prefix, flist in sorted(by_prefix.items()):
                print(f"   git rm {book_dir / parent_dir}/{prefix}_*.lean")

    # Print removals for empty directories
    print(f"\n3. Remove empty directories after git rm:")
    for parent_dir in sorted(sources_by_dir):
        print(f"   rmdir {book_dir / parent_dir}  # (if empty)")

    print(f"\n4. Run gen_sections.py to update Sections.lean and RouteTable.lean")
    print(f"5. Build to verify: cd ReasBook && lake build {book_name}")


if __name__ == "__main__":
    main()
