#!/usr/bin/env python3
"""Verify normalized ReasBook output against the original inventory.

Two verification modes:
  --quick    Structural checks + import-only detection + file counts (fast)
  --full     Above + content-preservation via git signatures (slower, comprehensive)

Usage:
    python3 scripts/verify_normalization.py --all --quick
    python3 scripts/verify_normalization.py AlgebraicTopology_May_1999 --full
    python3 scripts/verify_normalization.py --check-original-state
"""

import argparse
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from lib.section_map import BOOK_CONFIGS, get_config, NAME_MAPPING
from lib.inventory import read_inventory_from_git

REPO_ROOT = SCRIPT_DIR.parent
BOOKS_DIR = REPO_ROOT / "ReasBook" / "Books"
PER_STATEMENT_TYPES = {'three_level', 'two_level', 'roman', 'section_subdir', 'flat_chapter'}


# ── content-signature helpers ──────────────────────────────────────────────────

def _get_file_from_git(orig_path: str) -> str:
    """Get file content from 1a2c1941 via git show."""
    git_path = f"ReasBook/Books/{orig_path}"
    r = subprocess.run(
        ['git', 'show', f'1a2c1941:{git_path}'],
        capture_output=True, text=True,
    )
    return r.stdout if r.returncode == 0 else ""


def _extract_body(content: str) -> str:
    """Strip import headers and leading comments from a .lean file."""
    lines = content.split('\n')
    body = []
    in_body = False
    for line in lines:
        s = line.strip()
        if not in_body:
            if s.startswith('import ') or s == '' or s.startswith('--'):
                continue
            in_body = True
        if in_body:
            body.append(s)
    return '\n'.join(body)


def _extract_signature(body: str, min_len: int = 30) -> str:
    """Extract the first substantive Lean declaration as a content fingerprint."""
    if not body.strip():
        return ""
    lines = body.strip().split('\n')
    keywords = (
        'def ', 'theorem ', 'lemma ', '#check', 'variable', 'open ',
        'universe', 'example', 'noncomputable', 'section', 'recall',
        'classical', 'attribute', 'macro', 'elab', 'syntax', 'instance',
    )
    for i, line in enumerate(lines):
        s = line.strip()
        if not s or s.startswith('--') or s.startswith('/-'):
            continue
        if any(s.startswith(kw) for kw in keywords):
            sig = '\n'.join(lines[i:min(i + 4, len(lines))])
            if len(sig) >= min_len:
                return sig
    # fallback: first non-empty line of sufficient length
    for line in lines:
        s = line.strip()
        if s and len(s) >= min_len and not s.startswith('--') and not s.startswith('/-'):
            return s
    return ""


# ── verification functions ────────────────────────────────────────────────────

def verify_book_quick(new_name: str) -> dict:
    """Quick structural checks. Returns a dict of issues found."""
    original_name = None
    for orig, name in NAME_MAPPING.items():
        if name == new_name:
            original_name = orig
            break
    if not original_name:
        return {'error': f"Unknown book '{new_name}'"}

    config = get_config(original_name)
    book_dir = BOOKS_DIR / new_name
    chapters_dir = book_dir / "Chapters"
    issues = []

    if not book_dir.exists():
        return {'error': f"Directory not found: {book_dir}"}

    # 1. Directory structure
    if config['type'] not in ('library', 'empty'):
        if not (book_dir / "Book.lean").exists():
            issues.append("Missing Book.lean")
        if config['type'] != 'canonical' and not chapters_dir.exists():
            issues.append("Missing Chapters/ directory")
    for sd in config.get('shared_dirs', []):
        if not (book_dir / sd).exists():
            issues.append(f"Missing shared directory: {sd}/")

    # 2. Import-only sections
    import_only = []
    if chapters_dir.exists():
        for sf in chapters_dir.rglob("section*.lean"):
            content = sf.read_text(encoding='utf-8')
            lines = content.strip().split('\n')
            import_count = sum(1 for l in lines if l.startswith('import '))
            non_blank = sum(
                1 for l in lines
                if l.strip() and not l.startswith('import ') and not l.startswith('--')
            )
            if import_count > 0 and non_blank == 0:
                import_only.append(str(sf.relative_to(book_dir)))

    # 3. File count
    lean_count = len(list(book_dir.rglob("*.lean")))

    return {
        'new_name': new_name,
        'original_name': original_name,
        'book_type': config['type'],
        'issues': issues,
        'import_only': import_only,
        'lean_count': lean_count,
    }


def verify_book_full(new_name: str) -> dict:
    """Comprehensive content-preservation check against 1a2c1941 inventory."""
    result = verify_book_quick(new_name)
    if 'error' in result:
        return result

    original_name = result['original_name']
    config = get_config(original_name)
    chapters_dir = BOOKS_DIR / new_name / "Chapters"

    # Only check per-statement books
    if config['type'] not in PER_STATEMENT_TYPES:
        result['content_check'] = 'skipped (not a per-statement book)'
        return result

    # Build merged content index (normalized whitespace for fuzzy matching)
    all_content = ''
    if chapters_dir.exists():
        for sf in chapters_dir.rglob("section*.lean"):
            all_content += sf.read_text(encoding='utf-8') + '\n'
    all_content_norm = ' '.join(all_content.split())

    # Get original inventory
    git_inv = read_inventory_from_git()
    orig_files = git_inv.get(original_name, [])

    # Exclude root files
    skip_stems = {'Basic', 'Book', 'README'}
    stmt_files = [
        (f, Path(f).stem) for f in orig_files
        if Path(f).stem not in skip_stems and '/' in Path(f).as_posix()
    ]

    missing_content = []
    marker_only_found = 0

    for full_path, stem in stmt_files:
        # Fast path: marker match
        if f'### {stem}' in all_content:
            marker_only_found += 1
            continue

        # Content-signature path
        raw = _get_file_from_git(full_path)
        body = _extract_body(raw)
        if not body.strip():
            continue  # empty file — skip

        sig = _extract_signature(body)
        if not sig:
            missing_content.append((full_path, "no extractable signature"))
            continue

        sig_norm = ' '.join(sig.split())
        if sig_norm in all_content_norm:
            continue

        missing_content.append((full_path, "content signature not found"))

    result['content_check'] = {
        'total': len(stmt_files),
        'marker_found': marker_only_found,
        'signature_verified': len(stmt_files) - marker_only_found - len(missing_content),
        'missing': missing_content,
    }
    return result


def verify_all(quick_only: bool = True) -> bool:
    """Verify all books. Returns True if all pass."""
    all_ok = True
    for orig_name in sorted(BOOK_CONFIGS.keys()):
        new_name = BOOK_CONFIGS[orig_name]["new_name"]
        if quick_only:
            r = verify_book_quick(new_name)
        else:
            r = verify_book_full(new_name)
        ok = _print_result(r)
        if not ok:
            all_ok = False
    return all_ok


def check_original_state() -> bool:
    """Check that ReasBook/Books/ matches 1a2c1941 inventory."""
    print("Checking original state against 1a2c1941 inventory...\n")
    git_inventory = read_inventory_from_git()
    all_ok = True

    for orig_name, expected_files in sorted(git_inventory.items()):
        book_dir = BOOKS_DIR / orig_name
        if not book_dir.exists():
            print(f"  ❌ MISSING: {orig_name}/")
            all_ok = False
            continue

        actual_files = [
            str(p.relative_to(book_dir)) for p in sorted(book_dir.rglob("*.lean"))
        ]
        expected_set = set(expected_files)
        actual_set = set(actual_files)
        missing = expected_set - actual_set
        extra = actual_set - expected_set

        if missing or extra:
            print(f"  ⚠️  {orig_name}: {len(expected_files)} expected, {len(actual_files)} actual")
            if missing:
                print(f"      Missing: {list(missing)[:5]}...")
            if extra:
                print(f"      Extra: {list(extra)[:5]}...")
            all_ok = False
        else:
            print(f"  ✅ {orig_name}: {len(actual_files)} files (matches inventory)")

    return all_ok


def _print_result(r: dict) -> bool:
    """Print a verification result dict. Returns True if no issues."""
    if 'error' in r:
        print(f"  ❌ {r['error']}")
        return False

    issues = r.get('issues', [])
    import_only = r.get('import_only', [])

    ok = len(issues) == 0 and len(import_only) == 0

    status = "✅" if ok else "❌"
    print(f"\n{status} {r['new_name']} ({r['book_type']}) — {r['lean_count']} .lean files")

    for i in issues:
        print(f"     ❌ {i}")
    for io in import_only:
        print(f"     ❌ IMPORT-ONLY: {io}")

    cc = r.get('content_check')
    if isinstance(cc, dict):
        total = cc['total']
        marker = cc['marker_found']
        sig = cc['signature_verified']
        missing = cc['missing']
        pct = (marker + sig) / total * 100 if total else 0
        print(f"     Content: {marker}+{sig}/{total} ({pct:.1f}%)")
        if missing:
            print(f"     ⚠️  {len(missing)} files with unverified content")
            for m in missing[:3]:
                print(f"        {m[0]}: {m[1]}")
            if len(missing) > 3:
                print(f"        ... and {len(missing) - 3} more")
    elif isinstance(cc, str):
        print(f"     Content: {cc}")

    return ok


# ── CLI ────────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="Verify normalized ReasBook output")
    parser.add_argument("book", nargs="?", help="Book name (new name)")
    parser.add_argument("--all", action="store_true", help="Verify all books")
    parser.add_argument("--quick", action="store_true", default=True,
                        help="Quick structural check (default)")
    parser.add_argument("--full", action="store_true",
                        help="Full content-preservation check via git signatures")
    parser.add_argument("--check-original-state", action="store_true",
                        help="Check current state matches 1a2c1941 inventory")
    args = parser.parse_args()

    if args.check_original_state:
        success = check_original_state()
    elif args.all:
        if args.full:
            success = verify_all(quick_only=False)
        else:
            success = verify_all(quick_only=True)
    elif args.book:
        if args.full:
            r = verify_book_full(args.book)
        else:
            r = verify_book_quick(args.book)
        success = _print_result(r)
    else:
        parser.print_help()
        sys.exit(1)

    print(f"\n{'='*60}")
    print(f"Result: {'✅ PASS' if success else '❌ FAIL'}")
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
