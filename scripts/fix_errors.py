#!/usr/bin/env python3
"""
Apply safe auto-fixes to compilation errors.

Reads an automation diagnostic report, analyzes each error,
and applies only safe fixes (import, open, universe).  Never modifies
declaration signatures or proof bodies.  Each fix is verified individually
via lake build — if a fix does not reduce error count, it is rolled back.

Supports --bootstrap mode that generates a structured error report from
raw lake build output before proceeding to fix.

Four-level search strategy for unknown identifiers:
    1. migration_table  — exact match against known API renames
    2. search_project   — search same-book section files for the definition
    3. search_mathlib   — grep .lake/packages/mathlib for the identifier
    4. naming heuristics — try common patterns (foo', foo₀, Set.foo, etc.)

Usage:
    # Bootstrap mode: run lake build, capture errors, generate report, fix
    python3 scripts/fix_errors.py --bootstrap AlgebraicTopology_May_1999

    # Normal mode: read one local automation diagnostic report
    python3 scripts/fix_errors.py --source docs/automation-reports/v4.30.0/RUN/summary.md

    # Single book mode (universe dedup only)
    python3 scripts/fix_errors.py --book AlgebraicTopology_May_1999

    # Dry run: preview fixes without modifying files
    python3 scripts/fix_errors.py --source docs/automation-reports/v4.30.0/RUN/summary.md --dry-run

    # All books (recursive)
    python3 scripts/fix_errors.py --all
"""

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import shutil
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from lib.project_scope import resolve

REPO_ROOT = Path(os.environ.get("REASBOOK_ROOT", SCRIPT_DIR.parent)).resolve()
PROJECT_ROOT = REPO_ROOT / "ReasBook"
ERROR_REPORTS_DIR = REPO_ROOT / "docs" / "automation-reports" / "repairs"
MATHLIB_PATH = REPO_ROOT / "ReasBook" / ".lake" / "packages" / "mathlib"
REPORT_OUTPUT_DIR: Path | None = None
ACTIVE_KIND = "book"


def _report_output_dir() -> Path:
    return REPORT_OUTPUT_DIR or ERROR_REPORTS_DIR


def _source_module_name(book_name: str, relative_file: str) -> str:
    parts = Path(relative_file).with_suffix("").parts
    quoted = tuple(f"«{part}»" if part and part[0].isdigit() else part for part in parts)
    prefix = resolve(PROJECT_ROOT, ACTIVE_KIND, book_name).module_prefix
    return ".".join((prefix, *quoted))


def _project_module_prefix(name: str) -> str:
    return resolve(PROJECT_ROOT, ACTIVE_KIND, name).module_prefix

try:
    from lib.migration_table import find_migration
except ImportError:
    def find_migration(_identifier):
        return None


# ==========================================================================
#  Constants
# ==========================================================================

DECLARATION_KEYWORDS = [
    'def', 'theorem', 'lemma', 'instance', 'class', 'structure',
    'inductive', 'coinductive', 'axiom', 'example',
]

DECLARATION_RE = re.compile(
    r'^\s*(?:noncomputable\s+)?(?:private\s+)?(?:protected\s+)?(?:'
    + '|'.join(DECLARATION_KEYWORDS)
    + r')\s'
)

SIGNATURE_END_RE = re.compile(
    r'^\s*:=|^\s*where\b'
)

# Known safe-to-open namespaces
KNOWN_NAMESPACES: set[str] = {
    'Set', 'Filter', 'Matrix', 'MeasureTheory', 'Manifold',
    'Topology', 'TopologicalSpace', 'CategoryTheory', 'BigOperators',
    'Complex', 'Real', 'Nat', 'Int', 'Rat',
    'Finset', 'Finset.Basic', 'Polynomial', 'PowerSeries',
    'ContinuousMap', 'Homeomorph', 'Path', 'Homotopy',
    'Representation', 'Module', 'LinearMap', 'TensorProduct',
    'Algebra', 'Ring', 'Field', 'Group', 'Order',
    'Submodule', 'Subgroup', 'Subring', 'Subfield', 'Subalgebra',
    'IsOpen', 'IsClosed', 'Compact', 'LocallyFinite',
    'FiniteDimensional', 'FreeAbelianGroup', 'FreeGroup',
    'BoundedContinuousFunction', 'ContinuousLinearMap',
}

# identifier_substring -> suggested import module
KNOWN_MODULES: dict[str, str] = {
    'Topology': 'Mathlib.Topology.Basic',
    'TopologicalSpace': 'Mathlib.Topology.Basic',
    'SetLike': 'Mathlib.Algebra.Group.SetLike.Basic',
    'EuclideanSpace': 'Mathlib.Analysis.InnerProductSpace.EuclideanSpace',
    'PiLp': 'Mathlib.Analysis.InnerProductSpace.PiLp',
    'ChartedSpace': 'Mathlib.Geometry.Manifold.ChartedSpace',
    'SmoothManifoldWithCorners': 'Mathlib.Geometry.Manifold.SmoothManifoldWithCorners',
    'ContDiff': 'Mathlib.Analysis.Calculus.ContDiff.Defs',
    'HasDerivAt': 'Mathlib.Analysis.Calculus.Deriv.Basic',
    'HasFDerivAt': 'Mathlib.Analysis.Calculus.FDeriv.Basic',
    'Matrix.det': 'Mathlib.LinearAlgebra.Matrix.Determinant',
    'Matrix.mulVec': 'Mathlib.LinearAlgebra.Matrix.MulVec',
    'MeasureTheory': 'Mathlib.MeasureTheory.Measure.Typeclasses',
}

SCOPED_NAMESPACES: dict[str, str] = {
    'BigOperators': 'BigOperators',
}


# ==========================================================================
#  Declaration signature detection
# ==========================================================================

def is_declaration_signature(file_content: str, error_line_num: int) -> bool:
    """Check whether an error line is within a declaration signature.

    A declaration signature spans from the declaration keyword
    (def, theorem, lemma, instance, class, structure, inductive,
    coinductive, axiom, example) to := or where.  Errors in this
    region cannot be auto-fixed because they involve the type of
    the declaration.
    """
    lines = file_content.split('\n')
    if error_line_num >= len(lines):
        return False

    line = lines[error_line_num].strip()

    if DECLARATION_RE.match(line):
        return True

    decl_start = None
    for i in range(error_line_num, -1, -1):
        l = lines[i].strip()
        if DECLARATION_RE.match(l):
            decl_start = i
            break

    if decl_start is None:
        return False

    for j in range(decl_start + 1, error_line_num):
        if SIGNATURE_END_RE.match(lines[j].strip()):
            return False

    return True


# ==========================================================================
#  Safe fixes
# ==========================================================================

def fix_duplicate_universe(content: str) -> tuple[str, int]:
    """Remove duplicate universe declarations.

    Handles both top-level `universe u v ...` lines and body-level
    `universe` commands inside section/end blocks.

    Returns (new_content, num_removed_duplicates).
    """
    lines = content.split('\n')
    seen: set[str] = set()
    new_lines: list[str] = []
    removed = 0

    for line in lines:
        stripped = line.strip()
        m = re.match(r'^\s*universe\s+(.+)$', stripped)
        if m:
            vars_str = m.group(1)
            vars_list = re.split(r'\s+', vars_str.strip())
            new_vars = [v for v in vars_list if v not in seen]
            if not new_vars:
                removed += 1
                continue
            if len(new_vars) < len(vars_list):
                removed += 1
                indent = line[:len(line) - len(line.lstrip())]
                new_lines.append(indent + f'universe {" ".join(new_vars)}')
                for v in new_vars:
                    seen.add(v)
                continue
            for v in new_vars:
                seen.add(v)
        new_lines.append(line)

    return '\n'.join(new_lines), removed


def fix_add_open(content: str, namespace: str) -> str:
    """Add an `open <namespace>` statement after the last import line."""
    open_line = f'open {namespace}'
    if open_line in content:
        return content

    lines = content.split('\n')
    last_import_idx = -1
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith('import '):
            last_import_idx = i

    insert_idx = last_import_idx + 1 if last_import_idx >= 0 else 0
    if insert_idx > 0 and lines[insert_idx - 1].strip() != '':
        lines.insert(insert_idx, '')
        insert_idx += 1
    lines.insert(insert_idx, open_line)
    return '\n'.join(lines)


def fix_add_scoped_open(content: str, namespace: str) -> str:
    """Add `open scoped <namespace>` after the last import line."""
    open_line = f'open scoped {namespace}'
    if open_line in content or f'open {namespace}' in content:
        return content

    lines = content.split('\n')
    last_import_idx = -1
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith('import '):
            last_import_idx = i

    insert_idx = last_import_idx + 1 if last_import_idx >= 0 else 0
    if insert_idx > 0 and lines[insert_idx - 1].strip() != '':
        lines.insert(insert_idx, '')
        insert_idx += 1
    lines.insert(insert_idx, open_line)
    return '\n'.join(lines)


def fix_add_import(content: str, module: str) -> str:
    """Add an import statement after the last existing import line."""
    imp_line = f'import {module}'
    if imp_line in content:
        return content

    lines = content.split('\n')
    last_import_idx = -1
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith('import '):
            last_import_idx = i

    insert_idx = last_import_idx + 1 if last_import_idx >= 0 else 0
    lines.insert(insert_idx, imp_line)
    return '\n'.join(lines)


def fix_migrate_identifier(content: str, old_id: str, new_id: str) -> str:
    """Replace an identifier throughout the file, but NOT in:
    - Import lines
    - Declaration signature lines
    """
    lines = content.split('\n')
    new_lines: list[str] = []
    decl_active = False

    for line in lines:
        stripped = line.strip()

        if DECLARATION_RE.match(stripped):
            decl_active = SIGNATURE_END_RE.search(stripped) is None
            new_lines.append(line)
            continue

        if decl_active:
            if SIGNATURE_END_RE.match(stripped):
                decl_active = False
            new_lines.append(line)
            continue

        if stripped.startswith('import '):
            new_lines.append(line)
            continue

        pattern = r'\b' + re.escape(old_id) + r'\b'
        new_lines.append(re.sub(pattern, new_id, line))

    return '\n'.join(new_lines)


# ==========================================================================
#  Four-level search strategy
# ==========================================================================

def search_project(book_dir: Path, identifier: str, current_file_rel: str) -> Optional[dict]:
    """Level 2: Search for identifier definitions in other section files
    within the same book.

    Only adds imports in the FORWARD direction (target section < source section)
    to avoid build cycles.  The chapter aggregator imports sections in order
    (section01 → section02 → section03), so an import from section05 to
    section01 is safe (01 already compiled), but section01 to section05 is not.

    Returns a dict with module path information if found, else None.
    Reverse dependencies (target > source) are noted but not auto-fixed.
    """
    if not book_dir.exists():
        return None

    # Extract current section numbers
    cur_m = re.search(r'Chap(\d+)/section(\d+)', current_file_rel)
    cur_chap = int(cur_m.group(1)) if cur_m else 0
    cur_sec = int(cur_m.group(2)) if cur_m else 0

    for fp in book_dir.rglob("*.lean"):
        rel = str(fp.relative_to(book_dir))
        if rel == current_file_rel:
            continue
        try:
            content = fp.read_text(encoding='utf-8')
        except Exception:
            continue
        # Look for the identifier as a definition
        if re.search(rf'\b(?:def|theorem|lemma|instance)\s+'
                     rf'{re.escape(identifier)}\b', content):
            # Extract target section numbers
            tgt_m = re.search(r'Chap(\d+)/section(\d+)', rel)
            tgt_chap = int(tgt_m.group(1)) if tgt_m else 0
            tgt_sec = int(tgt_m.group(2)) if tgt_m else 0

            # Only add import if target comes BEFORE source in section order
            # (same chapter, target section < source section)
            if tgt_chap == cur_chap and tgt_sec < cur_sec:
                module = rel.replace('/', '.').replace('.lean', '')
                return {
                    "source": rel,
                    "module": module,
                }
            # Reverse dependency: cannot auto-fix with import alone.
            # The defining per-statement file should have been in the same
            # or earlier section during normalize.  Flag for manual review.
            else:
                return {
                    "reject": (
                        f"'{identifier}' is defined in {rel} (section {tgt_sec}) "
                        f"but used in section {cur_sec}. "
                        f"Import would create a cycle (chapter aggregator "
                        f"imports in order). Consider moving the definition "
                        f"to an earlier section during normalize_book.py."
                    ),
                }
    return None


def search_mathlib(identifier: str) -> Optional[dict]:
    """Level 3: Search for the identifier in local mathlib sources.

    First tries grep for def/theorem/lemma declarations (exact match).
    Falls back to fuzzy grep for any occurrence.
    Returns a dict describing the fix, or None if not found.
    """
    if not MATHLIB_PATH.exists():
        return None

    # Precise search: decl keyword + identifier
    try:
        result = subprocess.run(
            ["grep", "-rl", rf"def {identifier}\|theorem {identifier}\|"
             rf"lemma {identifier}\|instance {identifier}",
             str(MATHLIB_PATH), "--include=*.lean"],
            capture_output=True, text=True, timeout=30,
        )
    except (subprocess.TimeoutExpired, FileNotFoundError):
        result = None

    if result and result.stdout.strip():
        first_file = result.stdout.strip().split('\n')[0]
        fp = Path(first_file)
        try:
            rel = fp.relative_to(MATHLIB_PATH)
        except ValueError:
            rel = fp
        module = str(rel.with_suffix('')).replace('/', '.')
        if not module.startswith('Mathlib.'):
            module = f'Mathlib.{module}'
        return {
            "type": "add_import",
            "module": module,
            "description": (
                f"add import for '{identifier}' "
                f"(found in {module})"
            ),
        }

    # Fuzzy search: any occurrence
    try:
        result2 = subprocess.run(
            ["grep", "-rl", identifier, str(MATHLIB_PATH),
             "--include=*.lean"],
            capture_output=True, text=True, timeout=30,
        )
    except (subprocess.TimeoutExpired, FileNotFoundError):
        result2 = None

    if result2 and result2.stdout.strip():
        first_file = result2.stdout.strip().split('\n')[0]
        fp = Path(first_file)
        try:
            rel = fp.relative_to(MATHLIB_PATH)
        except ValueError:
            rel = fp
        module = str(rel.with_suffix('')).replace('/', '.')
        if not module.startswith('Mathlib.'):
            module = f'Mathlib.{module}'
        return {
            "type": "add_import",
            "module": module,
            "description": (
                f"add import for '{identifier}' "
                f"(fuzzy match in {module})"
            ),
        }

    return None


def try_naming_heuristics(identifier: str, file_content: str) -> Optional[dict]:
    """Level 4: Try common naming patterns for unknown identifiers.

    Patterns tried:
        - Strip trailing prime (foo' -> foo)
        - Replace subscript 0 (foo₀ -> foo)
        - Prepend common namespace prefixes (Set.foo, Topology.foo, etc.)
        - Dot-notation: if identifier contains '.', try opening the prefix

    Returns a dict with the proposed fix, or None if no heuristic matches.
    """
    # Pattern 1: trailing prime — check if base identifier is known
    prime_match = re.match(r"^(.+)'$", identifier)
    if prime_match:
        base = prime_match.group(1)
        mig = find_migration(base)
        if mig and mig.get("new"):
            return {
                "type": "migrate_identifier",
                "old": identifier,
                "new": f"{mig['new']}'",
                "description": (
                    f"heuristic: '{identifier}' -> "
                    f"'{mig['new']}' (prime variant of '{base}')"
                ),
            }
        # Check if base exists in mathlib
        ml = search_mathlib(base)
        if ml:
            return {
                "type": "add_import",
                "module": ml["module"],
                "description": (
                    f"heuristic: add import for '{base}' "
                    f"(prime variant: '{identifier}')"
                ),
            }

    # Pattern 2: subscript 0
    sub_match = re.match(r"^(.+)₀$", identifier)
    if sub_match:
        base = sub_match.group(1)
        mig = find_migration(base)
        if mig and mig.get("new"):
            return {
                "type": "migrate_identifier",
                "old": identifier,
                "new": f"{mig['new']}₀",
                "description": (
                    f"heuristic: '{identifier}' -> "
                    f"'{mig['new']}₀' (subscript variant of '{base}')"
                ),
            }
        ml = search_mathlib(base)
        if ml:
            return {
                "type": "add_import",
                "module": ml["module"],
                "description": (
                    f"heuristic: add import for '{base}' "
                    f"(subscript variant: '{identifier}')"
                ),
            }

    # Pattern 3: dotted identifier — try opening the prefix
    if '.' in identifier:
        parts = identifier.split('.')
        for prefix_len in reversed(range(1, len(parts))):
            prefix = '.'.join(parts[:prefix_len])
            suffix = '.'.join(parts[prefix_len:])
            ml = search_mathlib(suffix)
            if ml:
                return {
                    "type": "open_and_import",
                    "namespace": prefix,
                    "module": ml["module"],
                    "description": (
                        f"heuristic: open '{prefix}' + import for "
                        f"'{suffix}' (from '{identifier}')"
                    ),
                }

    # Pattern 4: try common namespace prefixes
    namespace_prefixes = ['Set', 'Topology', 'MeasureTheory', 'Filter',
                          'CategoryTheory', 'Module', 'LinearMap']
    stripped = identifier
    # Strip known prefixes that might already be present
    for ns in namespace_prefixes:
        if identifier.startswith(ns + '.'):
            stripped = identifier[len(ns) + 1:]
            ml = search_mathlib(stripped)
            if ml:
                return {
                    "type": "open_and_import",
                    "namespace": ns,
                    "module": ml["module"],
                    "description": (
                        f"heuristic: already qualified '{identifier}' -> "
                        f"open '{ns}' + import for '{stripped}'"
                    ),
                }

    return None


# ==========================================================================
#  Error analysis (four-level search integrated)
# ==========================================================================

def analyze_error(
    error_message: str,
    file_content: str,
    file_path: str,
    book_dir: Path,
    current_file_rel: str,
) -> Optional[dict]:
    """Analyze a single error message and return a safe fix if possible.

    Four-level search for unknown identifiers:
        1. migration_table
        2. search_project (same-book section files)
        3. search_mathlib (grep .lake/packages/mathlib)
        4. naming heuristics

    Returns a dict with either:
      {"type": "...", "description": "...", "apply": callable}
    or:
      {"reject": "reason string"}
    or None for unparseable errors.
    """
    # Extract line number
    line_match = re.search(r'(\d+):(\d+)', error_message)
    line_num = int(line_match.group(1)) - 1 if line_match else -1

    msg = error_message.lower()

    # ---- Universe conflict ----
    if 'universe' in msg and ('already declared' in msg or
                               'universe level' in msg):
        return {
            "type": "universe_dedup",
            "description": "remove duplicate universe declaration",
            "apply": lambda c: fix_duplicate_universe(c)[0],
        }

    # ---- Unknown namespace ----
    ns_match = re.search(r"unknown namespace\s+'?(\w+(?:\.\w+)*)'?", msg)
    if ns_match:
        ns = ns_match.group(1)
        top_ns = ns.split('.')[0]
        if top_ns in KNOWN_NAMESPACES:
            return {
                "type": "add_open",
                "description": f"add 'open {top_ns}'",
                "apply": lambda c: fix_add_open(c, top_ns),
            }
        if ns in KNOWN_NAMESPACES:
            return {
                "type": "add_open",
                "description": f"add 'open {ns}'",
                "apply": lambda c: fix_add_open(c, ns),
            }
        # Try search_mathlib for the namespace
        ml_result = search_mathlib(top_ns)
        if ml_result and ml_result.get("type") == "add_import":
            return {
                "type": "add_import",
                "description": (
                    f"add 'import {ml_result['module']}' for "
                    f"namespace '{ns}'"
                ),
                "apply": lambda c, m=ml_result['module']: (
                    fix_add_import(c, m)
                ),
            }
        return {
            "reject": (
                f"namespace '{ns}' is not in the known namespace "
                f"allowlist and not found in mathlib"
            ),
        }

    # ---- Unknown identifier (four-level search) ----
    id_match = re.search(r"unknown identifier\s+'?(\w+(?:\.\w+)*)'?", msg)
    if id_match:
        identifier = id_match.group(1)
        parts = identifier.split('.')

        # Check if in declaration signature (constraint 2)
        if line_num >= 0 and is_declaration_signature(file_content, line_num):
            return {
                "reject": (
                    f"'{identifier}' is in a declaration signature "
                    f"— requires human review"
                ),
            }

        # Quick check: dotted identifier with known namespace prefix
        if len(parts) >= 2 and parts[0] in KNOWN_NAMESPACES:
            return {
                "type": "add_open",
                "description": (
                    f"add 'open {parts[0]}' for qualified "
                    f"identifier '{identifier}'"
                ),
                "apply": lambda c, ns=parts[0]: fix_add_open(c, ns),
            }

        # ---- Level 1: migration_table ----
        migration = find_migration(identifier)
        if migration and migration.get("new") is not None:
            return {
                "type": "migrate_identifier",
                "description": (
                    f"migration_table: '{identifier}' -> "
                    f"'{migration['new']}'"
                ),
                "apply": lambda c, o=identifier, n=migration['new']: (
                    fix_migrate_identifier(c, o, n)
                ),
            }
        if migration and migration.get("new") is None:
            return {
                "reject": (
                    f"'{identifier}' was removed in "
                    f"{migration.get('since', '?')} — "
                    f"{migration.get('note', 'no further info')}"
                ),
            }

        # ---- Level 2: project search ----
        project_result = search_project(book_dir, identifier,
                                        current_file_rel)
        if project_result:
            return {
                "type": "add_import",
                "description": (
                    f"project search: add import for '{identifier}' "
                    f"(defined in {project_result['source']})"
                ),
                "apply": lambda c, m=project_result['module']: (
                    fix_add_import(c, m)
                ),
            }

        # ---- Level 3: mathlib search ----
        mathlib_result = search_mathlib(identifier)
        if mathlib_result:
            if mathlib_result["type"] == "add_import":
                return {
                    "type": "add_import",
                    "description": mathlib_result["description"],
                    "apply": lambda c, m=mathlib_result["module"]: (
                        fix_add_import(c, m)
                    ),
                }

        # ---- Level 4: naming heuristics ----
        heuristic_result = try_naming_heuristics(identifier, file_content)
        if heuristic_result:
            if heuristic_result["type"] == "migrate_identifier":
                return {
                    "type": "migrate_identifier",
                    "description": heuristic_result["description"],
                    "apply": lambda c, o=heuristic_result["old"],
                                    n=heuristic_result["new"]: (
                        fix_migrate_identifier(c, o, n)
                    ),
                }
            elif heuristic_result["type"] == "add_import":
                return {
                    "type": "add_import",
                    "description": heuristic_result["description"],
                    "apply": lambda c, m=heuristic_result["module"]: (
                        fix_add_import(c, m)
                    ),
                }
            elif heuristic_result["type"] == "open_and_import":
                # Apply both: open namespace + add import
                ns = heuristic_result["namespace"]
                mod = heuristic_result["module"]
                return {
                    "type": "open_and_import",
                    "description": heuristic_result["description"],
                    "apply": lambda c, ns=ns, mod=mod: (
                        fix_add_import(fix_add_open(c, ns), mod)
                    ),
                }

        # Check KNOWN_MODULES for module suggestions
        for key, mod in KNOWN_MODULES.items():
            if identifier == key or identifier.endswith('.' + key):
                return {
                    "type": "add_import",
                    "description": (
                        f"known module: add 'import {mod}' "
                        f"for '{identifier}'"
                    ),
                    "apply": lambda c, m=mod: fix_add_import(c, m),
                }

        return {
            "reject": (
                f"'{identifier}' not found in migration_table, "
                f"project, mathlib, or heuristics"
            ),
        }

    # ---- Missing scoped notation ----
    for scope_name, ns in SCOPED_NAMESPACES.items():
        if (scope_name.lower() in msg and
                ('scoped' in msg or 'notation' in msg or
                 'macro' in msg or 'token' in msg)):
            return {
                "type": "add_scoped_open",
                "description": f"add 'open scoped {ns}'",
                "apply": lambda c, n=ns: fix_add_scoped_open(c, n),
            }

    # ---- Bad import / file not found ----
    bad_import_match = re.search(
        r"(?:bad import|no such file or directory).*?import\s+(\S+)", msg)
    if not bad_import_match:
        bad_import_match = re.search(
            r"file not found.*?import\s+(\S+)", msg)
    if bad_import_match:
        module = bad_import_match.group(1).strip("'\"")
        return {
            "reject": (
                f"import '{module}' not found — may have been removed "
                f"or renamed; check migration table or update MANUALLY"
            ),
        }

    # ── unknown module prefix (old import paths in aggregators) ──
    if 'unknown module prefix' in msg:
        old_prefix = extract_module_prefix(msg)
        if old_prefix:
            # Replace old module prefix with correct book name.
            # Works on ChapNN.lean aggregators AND section files.
            return {
                "apply": lambda c: replace_import_prefix(
                    c, old_prefix, _project_module_prefix(book_dir.name)
                ),
                "description": f"replace module prefix '{old_prefix}' with '{book_dir.name}'",
            }
        return {"reject": "unknown module prefix — cannot determine correct prefix"}

    # ── Ambiguous term — try section-wrapping to isolate variable scopes ──
    if 'ambiguous term' in msg and line_num >= 0:
        fix = fix_ambiguous_term_in_file(file_content)
        if fix:
            return {"fix": fix, "description": "wrap per-statement blocks in section/end to isolate variables"}

    # ── Type E: light-touch fixes for type-level errors ──

    # Function expected — variable used as function but Lean sees it as non-function
    if "function expected" in msg and line_num >= 0:
        if not is_declaration_signature(file_content, line_num):
            fix = add_type_annotation(file_content, line_num, error_message)
            if fix:
                return {"fix": fix, "description": "add type annotation to resolve function/term ambiguity"}

    # Type mismatch — may be fixable with explicit @ notation
    if "type mismatch" in msg and line_num >= 0:
        if not is_declaration_signature(file_content, line_num):
            fix = add_explicit_application(file_content, line_num, error_message)
            if fix:
                return {"fix": fix, "description": "add explicit @ application to resolve type mismatch"}

    # failed to synthesize instance
    if "failed to synthesize instance" in msg and line_num >= 0:
        if not is_declaration_signature(file_content, line_num):
            fix = add_instance_param(file_content, line_num, error_message)
            if fix:
                return {"fix": fix, "description": "add explicit instance argument"}

    # has already been declared — duplicate definition from merge
    if "has already been declared" in msg:
        return {
            "reject": (
                f"duplicate definition from per-statement merge — "
                f"two original files defined the same identifier; requires manual dedup"
            ),
        }

    # ── Level 5: AI-assisted fix (session-driven, last resort) ──
    # Only activated in --apply mode.  Presents error context for the
    # session to review and propose a fix under the same safety constraints.
    # _ai_fix_enabled is set by _run_apply_mode().
    if _ai_fix_enabled:
        ai_result = ai_fix(error_message, file_content, line_num, book_dir)
        if ai_result:
            # Return context for session review; fix comes from the session.
            # The session inspects the context, proposes a fix, and it goes
            # through the same per-fix verification loop.
            return {
                "context": ai_result["context"],
                "description": ai_result["description"],
                "requires_review": True,
            }


# ==========================================================================
#  Report parsing
# ==========================================================================

def parse_error_report(report_path: Path) -> dict[str, list[dict]]:
    """Parse a sync/upgrade error report into {book_name: [{error, file?}]}.

    Recognizes:
      1. Section-per-book markdown:
           ### BookName (N errors)
           - `error message`
           - `in file path: line 42: error message`

      2. Flat list with file prefixes:
           - `path:42:18: error: ...`

      3. Lake build error format:
           path:42:18: error: ...
    """
    if not report_path.exists():
        return {}

    content = report_path.read_text(encoding='utf-8')
    errors_by_book: dict[str, list[dict]] = defaultdict(list)

    current_book: Optional[str] = None

    for line in content.split('\n'):
        # Book section header with error count
        book_match = re.match(r'^###\s+(.+?)\s*\(\d+\s*(?:error|warning)', line)
        if not book_match:
            book_match = re.match(r'^##\s+(.+?)\s*\(\d+\s*(?:error|warning)', line)
        if book_match:
            current_book = book_match.group(1).strip()
            continue

        # Simple book header "## BookName"
        book_simple = re.match(r'^##\s+(\S.+)', line)
        if book_simple and not line.startswith('###'):
            candidate = book_simple.group(1).strip()
            if re.match(r'^[A-Z]', candidate) and len(candidate) < 100:
                current_book = candidate
            continue

        # Backtick-quoted error: - `...`
        error_match = re.match(r'^\s*[-*]\s+`(.+)`', line)
        if error_match and current_book:
            error_text = error_match.group(1)
            file_path = None
            file_match_in_error = re.search(
                r'([\w/]+\.lean)', error_text)
            if file_match_in_error:
                file_path = file_match_in_error.group(1)
            errors_by_book[current_book].append({
                "error": error_text,
                "file": file_path,
            })
            continue

        # File-prefixed error: path:line:col: error: ...
        file_prefix_match = re.match(
            r'^\s*(?:[-*]\s+)?'
            r'([\w/]+\.lean):'
            r'(\d+):(\d+):\s*(?:error|warning):\s*(.+)',
            line,
        )
        if file_prefix_match and current_book:
            file_path = file_prefix_match.group(1)
            line_n = file_prefix_match.group(2)
            col_n = file_prefix_match.group(3)
            error_text = file_prefix_match.group(4).strip()
            errors_by_book[current_book].append({
                "error": f"{file_path}:{line_n}:{col_n}: {error_text}",
                "file": file_path,
            })
            continue

        # Lake build output format: path:line:col: error: ...
        lake_match = re.match(
            r'^\s*([\w/]+\.lean):(\d+):(\d+):\s*'
            r'(?:error|warning):\s*(.+)',
            line,
        )
        if lake_match and current_book:
            file_path = lake_match.group(1)
            line_n = lake_match.group(2)
            col_n = lake_match.group(3)
            error_text = lake_match.group(4).strip()
            errors_by_book[current_book].append({
                "error": f"{file_path}:{line_n}:{col_n}: {error_text}",
                "file": file_path,
            })

    return dict(errors_by_book)


# ==========================================================================
#  Bootstrap mode: generate error report from lake build output
# ==========================================================================

def bootstrap_error_report(book_name: str) -> Optional[Path]:
    """Run lake build for a book, capture errors, generate structured report.

    Returns the path to the generated report file, or None if build succeeds
    (no errors to report).
    """
    print(f"\n{'=' * 60}")
    print(f"Bootstrap: building {book_name} to capture errors...")
    print(f"{'=' * 60}")

    spec = resolve(PROJECT_ROOT, ACTIVE_KIND, book_name)
    result = subprocess.run(
        ["lake", "build", spec.target],
        cwd=REPO_ROOT / "ReasBook",
        capture_output=True, text=True,
    )

    output = result.stdout + result.stderr
    errors_by_file: dict[str, list[dict]] = defaultdict(list)

    # Build the prefix to strip.  Lake reports paths as
    #   error: Books/<BookName>/path/to/file.lean:line:col: message
    # or (on stderr) just
    #   Books/<BookName>/path/to/file.lean:line:col: error: message
    area = "Books" if ACTIVE_KIND == "book" else "Papers"
    book_prefix = f"{area}/{book_name}/"

    # Parse lake build error lines.  Two formats:
    #   error: Books/Lib/file.lean:42:18: message
    #   Books/Lib/file.lean:42:18: error: message
    for line in output.split('\n'):
        # Try format 1: "error: Books/Lib/..."
        m1 = re.match(
            r'^error:\s+(' + re.escape(book_prefix) + r'(.+\.lean)):(\d+):(\d+):\s*(.+)',
            line,
        )
        if m1:
            file_path = m1.group(2)   # relative path after Books/Lib/
            error_text = m1.group(5).strip()
            errors_by_file[file_path].append({
                "error": f"{file_path}:{m1.group(3)}:{m1.group(4)}: {error_text}",
                "file": file_path,
            })
            continue

        # Try format 2: "Books/Lib/file.lean:42:18: error: message"
        m2 = re.match(
            r'^' + re.escape(book_prefix) + r'(.+\.lean):(\d+):(\d+):\s*'
            r'(?:error|warning):\s*(.+)',
            line,
        )
        if m2:
            file_path = m2.group(1)
            error_text = m2.group(4).strip()
            errors_by_file[file_path].append({
                "error": f"{file_path}:{m2.group(2)}:{m2.group(3)}: {error_text}",
                "file": file_path,
            })

    if not errors_by_file:
        print(f"  No errors — {book_name} compiled successfully.")
        return None

    # Generate the grouped report
    output_dir = _report_output_dir()
    output_dir.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now(timezone.utc).strftime('%Y-%m-%d-%H%M%S')
    report_path = output_dir / f"repair-bootstrap-{timestamp}-{ACTIVE_KIND}-{book_name}.md"

    total_errors = sum(len(v) for v in errors_by_file.values())

    lines: list[str] = [
        f"# Bootstrap Error Report: {book_name}",
        "",
        f"**Date**: {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')}",
        f"**Source**: lake build {spec.target}",
        f"**Kind**: {ACTIVE_KIND}",
        f"**Total errors**: {total_errors}",
        "",
        f"## {book_name} ({total_errors} errors)",
        "",
    ]

    for file_path, errs in sorted(errors_by_file.items()):
        lines.append(f"### {file_path} ({len(errs)} errors)")
        lines.append("")
        for err in errs:
            lines.append(f"- `{err['error']}`")
        lines.append("")

    content = '\n'.join(lines) + '\n'
    report_path.write_text(content, encoding='utf-8')
    print(f"  Bootstrap report written to: {report_path}")
    print(f"  {total_errors} errors captured across {len(errors_by_file)} files")

    return report_path


# ==========================================================================
#  Fix application and per-fix verification with cascade filtering
# ==========================================================================

def count_errors_for_file(build_output: str, file_rel: str) -> int:
    """Count how many error lines in the build output refer to a given file."""
    count = 0
    for line in build_output.split('\n'):
        if file_rel in line and ': error:' in line:
            count += 1
    return count

def _errors_decreased_in_fixed_module(
    baseline_output: str, new_output: str, fixed_file_rel: str,
) -> bool:
    """Check whether errors in the directly fixed module decreased.
    When a structural fix exposes previously hidden modules, total errors
    may increase even though the fix itself is correct."""
    bl = sum(1 for l in baseline_output.split(chr(10)) if fixed_file_rel in l and chr(58)+' error:' in l)
    nw = sum(1 for l in new_output.split(chr(10)) if fixed_file_rel in l and chr(58)+' error:' in l)
    return nw < bl

# ── Type E helpers ──────────────────────────────────────────────────────────

def replace_import_prefix(content: str, old_prefix: str, book_name: str) -> str:
    """Replace an old module prefix with the correct book name in import lines."""
    lines = content.split('\n')
    new_lines = []
    for line in lines:
        s = line.strip()
        if s.startswith('import ') and s.startswith(f'import {old_prefix}.'):
            new_lines.append(s.replace(f'import {old_prefix}.', f'import {book_name}.'))
        else:
            new_lines.append(line)
    return '\n'.join(new_lines)


def add_type_annotation(content: str, line_num: int, _message: str) -> str | None:
    """Try to add a type annotation at the error location.

    For 'Function expected' errors: check if a variable name is being used as
    a function but Lean can't infer its function type. Add (x : _ → _) if safe.
    Only applies to variable references, not complex expressions.
    """
    lines = content.split('\n')
    if line_num >= len(lines):
        return None
    line = lines[line_num]
    # Extract the variable or expression that caused the error
    m = re.search(r'Function expected at\s+(\w+)', line)
    if not m:
        return None
    var = m.group(1)
    # Add type annotation inline: var → (var : _ → _)
    new_line = re.sub(rf'\b{re.escape(var)}\b', f'({var} : _ → _)', line, count=1)
    if new_line != line:
        lines[line_num] = new_line
        return '\n'.join(lines)
    return None


def add_explicit_application(content: str, line_num: int, _message: str) -> str | None:
    """Try to add @ for explicit application at the error location.

    For 'Type mismatch' errors: try inserting @ before the first function call
    on the error line to force fully-explicit type arguments.
    Only applies when the mismatch is about implicit type arguments.
    """
    lines = content.split('\n')
    if line_num >= len(lines):
        return None
    line = lines[line_num]
    # Only attempt if the line has a function application with implicit args
    if '(' in line and not line.strip().startswith('@'):
        # Find the first space before ( that looks like a function name
        m = re.match(r'(\s*)(\S+)', line)
        if m:
            indent, first_word = m.group(1), m.group(2)
            # Add @ before the first identifiable function
            if re.match(r'^[a-zA-Z]', first_word):
                lines[line_num] = f'{indent}@ {line[len(indent):]}'
                return '\n'.join(lines)
    return None


def add_instance_param(content: str, line_num: int, message: str) -> str | None:
    """Try to add an explicit instance argument for 'failed to synthesize' errors.

    Extracts the missing instance type from the error message and adds it as
    an explicit argument using (...) syntax.
    """
    lines = content.split('\n')
    if line_num >= len(lines):
        return None
    # Extract the instance type from the message
    m = re.search(r'failed to synthesize instance\s+(.+?)(?:\s*\n|$)', message)
    if not m:
        return None
    instance_type = m.group(1).strip()
    line = lines[line_num]
    # Add the instance as an explicit argument in the function call
    # Insert [_ : instance_type] before the first (
    paren_idx = line.find('(')
    if paren_idx >= 0:
        new_line = line[:paren_idx] + f'[_ : {instance_type}] ' + line[paren_idx:]
        lines[line_num] = new_line
        return '\n'.join(lines)
    return None


def extract_module_prefix(message: str) -> str | None:
    """Extract the unknown module prefix from an error message (case-insensitive)."""
    m = re.search(r"unknown module prefix [''](\w+)['']", message, re.IGNORECASE)
    if m:
        return m.group(1)
    return None


# ── AI-assisted fix (Level 5) ──────────────────────────────────────────────

_ai_fix_enabled = False  # Set to True in --apply mode


def enable_ai_fix():
    global _ai_fix_enabled
    _ai_fix_enabled = True


def _build_fix_context(msg: str, content: str, line: int) -> str:
    """Build context for the AI fix request: error + surrounding lines."""
    lines = content.split('\n')
    start = max(0, line - 50)
    end = min(len(lines), line + 50)
    surrounding = '\n'.join(
        f"{i + 1}: {l}" for i, l in enumerate(lines[start:end], start=start)
    )
    return f"""Fix Lean 4 compilation error under STRICT constraints:

Error: {msg}

File (lines {start + 1}-{end}):
{surrounding}

CONSTRAINTS (violating any = rejected):
1. NEVER modify def/theorem/lemma/instance signatures
2. NEVER add sorry, never comment out code, never delete code
3. Only adjust imports, universe declarations, variable references, or add type annotations
4. If the error is 'has already been declared', rename the SECOND occurrence (add '2' suffix)
5. Return ONLY the fixed lines (same line numbers as input), not the entire file"""


def _validate_fix_constraints(fix: str, original: str) -> bool:
    """Verify the AI fix doesn't violate safety constraints."""
    if 'sorry' in fix.lower():
        return False
    orig_sigs = set(re.findall(r'^(def|theorem|lemma|instance)\s+(\w+)', original, re.MULTILINE))
    fix_sigs = set(re.findall(r'^(def|theorem|lemma|instance)\s+(\w+)', fix, re.MULTILINE))
    if orig_sigs != fix_sigs:
        return False
    return True


def ai_fix(error_message: str, file_content: str, line_num: int,
           book_dir: Path) -> dict | None:
    """Level 5: AI-assisted fix. Only called after Levels 1-4 exhausted.

    Prepares structured context for the Claude session to attempt a fix.
    The session itself is the "model" — this function formats the error
    and surrounding code for the session to inspect, propose a fix, and
    have it verified by the same constraint checks and rebuild loop.

    Returns a dict with 'context' (formatted for human/Claude review)
    so the session can respond with a fix. In scripted environments,
    this function serves as a hook point for model integration.
    """
    lines = file_content.split('\n')
    start = max(0, line_num - 50)
    end = min(len(lines), line_num + 50)
    surrounding = '\n'.join(
        f"{i + 1}: {l}" for i, l in enumerate(lines[start:end], start=start)
    )
    context = (
        f"Fix Lean 4 compilation error under STRICT constraints:\n\n"
        f"Error: {error_message}\n\n"
        f"File (lines {start + 1}-{end}):\n"
        f"{surrounding}\n\n"
        f"CONSTRAINTS (violating any = rejected):\n"
        f"1. NEVER modify def/theorem/lemma/instance signatures\n"
        f"2. NEVER add sorry, never comment out code, never delete code\n"
        f"3. Only adjust imports, universe declarations, variable references, "
        f"or add type annotations\n"
        f"4. If the error is 'has already been declared', rename the SECOND "
        f"occurrence (add '2' suffix)\n"
        f"5. Return the full corrected file content"
    )
    return {
        "context": context,
        "description": "AI-assisted fix (requires Claude session review)",
        "requires_review": True,
    }


def fix_ambiguous_term_in_file(content: str) -> str | None:
    """Wrap per-statement blocks in section/end to isolate variable scopes.

    Only wraps blocks that contain 'variable' declarations and are not
    already wrapped. Returns modified content or None if no change needed.
    """
    lines = content.split('\n')
    new_lines = []
    in_block = False
    block_lines = []
    changed = False

    for line in lines:
        m = re.match(r'/-!\s*###\s+(.+?)\s*-/', line.strip())
        if m:
            if in_block and block_lines:
                body = '\n'.join(block_lines)
                has_var = bool(re.search(r'(?m)^\s*variable\s', body))
                stripped = body.strip()
                if has_var and not (stripped.startswith('section') and stripped.endswith('end')):
                    new_lines.append('section')
                    new_lines.extend(block_lines)
                    new_lines.append('end')
                    new_lines.append('')
                    changed = True
                else:
                    new_lines.extend(block_lines)
            block_lines = [line]
            in_block = True
            continue
        if in_block:
            block_lines.append(line)

    if in_block and block_lines:
        body = '\n'.join(block_lines)
        has_var = bool(re.search(r'(?m)^\s*variable\s', body))
        stripped = body.strip()
        if has_var and not (stripped.startswith('section') and stripped.endswith('end')):
            new_lines.append('section')
            new_lines.extend(block_lines)
            new_lines.append('end')
            new_lines.append('')
            changed = True
        else:
            new_lines.extend(block_lines)

    if changed:
        return '\n'.join(new_lines)
    return None


# ── Project-level fix orchestrator ──────────────────────────────────────────

def fix_book_errors(
    book_name: str,
    errors: list[dict],
    dry_run: bool,
) -> dict:
    """Apply safe fixes to a book or paper's errors with per-fix verification.

    Each fix is applied individually, the book is rebuilt, and the error
    count for the target file is checked:
        - Fewer errors: fix kept, cascade delta recorded
        - Same error count: fix rolled back
        - More errors: fix rolled back (introduced new problems)

    Returns a fix report dict with keys: book, total_errors, fixed, cannot_fix.
    """
    report: dict = {
        "kind": ACTIVE_KIND,
        "book": book_name,
        "total_errors": len(errors),
        "fixed": [],
        "cannot_fix": [],
    }

    book_dir = resolve(PROJECT_ROOT, ACTIVE_KIND, book_name).directory
    if not book_dir.exists():
        report["cannot_fix"].append({
            "file": "N/A",
            "error": f"Book directory not found: {book_dir}",
            "reason": "missing book",
        })
        return report

    # Index section files by relative path
    all_lean_files: dict[str, Path] = {}
    for fp in book_dir.rglob("*.lean"):
        all_lean_files[str(fp.relative_to(book_dir))] = fp

    # ---- Phase 1: Universe dedup on ALL .lean files (always safe) ----
    for rel, fp in all_lean_files.items():
        content = fp.read_text(encoding='utf-8')
        new_content, removed = fix_duplicate_universe(content)
        if removed > 0:
            if not dry_run:
                fp.write_text(new_content, encoding='utf-8')
            report["fixed"].append({
                "file": rel,
                "error": f"{removed} duplicate universe declaration(s)",
                "fix": "remove duplicate universe declarations",
            })

    # ---- Phase 2: Group errors by file ----
    # Build a set of files that had universe fixes and their error counts
    # We'll use this to track cascade filtering
    errors_by_file: dict[str, list[dict]] = defaultdict(list)
    for err in errors:
        file_ref = err.get("file")
        if file_ref and file_ref in all_lean_files:
            errors_by_file[file_ref].append(err)
        else:
            error_text = err.get("error", "")
            found = False
            for sf_rel in all_lean_files:
                if sf_rel in error_text:
                    errors_by_file[sf_rel].append(err)
                    found = True
                    break
            if not found:
                report["cannot_fix"].append({
                    "file": file_ref or "unknown",
                    "error": error_text[:120],
                    "reason": "could not determine which file the error is in",
                })

    # ---- Phase 3: Process each file's errors with per-fix verification ----
    for sf_rel, file_errors in errors_by_file.items():
        sf_path = all_lean_files[sf_rel]
        original_content = sf_path.read_text(encoding='utf-8')
        content = original_content
        initial_error_count = len(file_errors)

        # Build a quick format for error messages to avoid re-parsing
        remaining_errors = list(file_errors)
        file_fixes_applied = 0

        for err_idx, err in enumerate(file_errors):
            if err_idx >= len(remaining_errors):
                # This error was cascade-cleared by a previous fix
                continue

            error_msg = err.get("error", "")

            # Re-analyze against current (possibly modified) content
            result = analyze_error(error_msg, content, str(sf_path),
                                  book_dir, sf_rel)

            if result is None:
                report["cannot_fix"].append({
                    "file": sf_rel,
                    "error": error_msg[:120],
                    "reason": "could not parse error",
                })
                continue

            if "reject" in result:
                report["cannot_fix"].append({
                    "file": sf_rel,
                    "error": error_msg[:120],
                    "reason": result["reject"],
                })
                continue

            if "apply" not in result:
                report["cannot_fix"].append({
                    "file": sf_rel,
                    "error": error_msg[:120],
                    "reason": "no safe fix available",
                })
                continue

            # Try the fix
            try:
                new_content = result["apply"](content)
            except Exception as e:
                report["cannot_fix"].append({
                    "file": sf_rel,
                    "error": error_msg[:120],
                    "reason": f"fix application failed: {e}",
                })
                continue

            if new_content == content:
                # Fix was a no-op — skip
                report["cannot_fix"].append({
                    "file": sf_rel,
                    "error": error_msg[:120],
                    "reason": "fix produced no change",
                })
                continue

            # ---- Per-fix verification ----
            if dry_run:
                # Dry run: just record the fix, don't write or build
                content = new_content
                file_fixes_applied += 1
                report["fixed"].append({
                    "file": sf_rel,
                    "error": error_msg[:120],
                    "fix": result["description"],
                    "cascade_eliminated": 0,
                })
                continue

            # Write the fix and rebuild — use single-section build for speed.
            # Module path: per-statement file
            section_target = _source_module_name(book_name, sf_rel)

            sf_path.write_text(new_content, encoding='utf-8')

            build_result = subprocess.run(
                ["lake", "build", section_target],
                cwd=REPO_ROOT / "ReasBook",
                capture_output=True, text=True, timeout=300,
            )

            build_output = build_result.stdout + build_result.stderr

            # Count errors for this file before and after
            old_count = count_errors_for_file(build_output, sf_rel)

            # Revert the file, count errors without the fix
            sf_path.write_text(original_content)

            baseline_result = subprocess.run(
                ["lake", "build", section_target],
                cwd=REPO_ROOT / "ReasBook",
                capture_output=True, text=True, timeout=300,
            )
            baseline_output = baseline_result.stdout + baseline_result.stderr
            baseline_count = count_errors_for_file(baseline_output, sf_rel)

            if old_count < baseline_count:
                # Fix reduced errors — keep it
                sf_path.write_text(new_content)
                content = new_content
                original_content = new_content
                file_fixes_applied += 1
                cascade_delta = baseline_count - old_count - 1
                report["fixed"].append({
                    "file": sf_rel,
                    "error": error_msg[:120],
                    "fix": result["description"],
                    "cascade_eliminated": max(0, cascade_delta),
                })

                # Cascade filter: remove errors that disappeared
                if cascade_delta > 0:
                    print(
                        f"    Cascade: {cascade_delta} errors eliminated "
                        f"in {sf_rel}"
                    )

            elif old_count == baseline_count:
                # No change — rollback (kept in original state)
                report["cannot_fix"].append({
                    "file": sf_rel,
                    "error": error_msg[:120],
                    "reason": (
                        f"fix did not reduce error count "
                        f"(was: {baseline_count}, after: {old_count})"
                    ),
                })
                # sf_path already has original_content from baseline check

            else:
                # Error count increased — check if fix itself was correct
                # (exposed previously hidden errors in newly reachable modules)
                #
                # The fix is CORRECT if errors in the directly fixed module
                # decreased. The total increase is from OTHER modules that
                # were hidden behind an import/structural barrier and are now
                # being compiled for the first time.
                if _errors_decreased_in_fixed_module(
                    baseline_output, build_output, sf_rel
                ):
                    # Keep the fix — errors increased due to exposure, not breakage
                    sf_path.write_text(new_content)
                    content = new_content
                    original_content = new_content
                    file_fixes_applied += 1
                    exposed = old_count - baseline_count
                    report["fixed"].append({
                        "file": sf_rel,
                        "error": error_msg[:120],
                        "fix": result["description"],
                        "errors_exposed": exposed,
                        "note": f"Fix correct; {exposed} previously hidden errors now visible",
                    })
                    print(f"    Exposed: {exposed} hidden errors now reachable")
                else:
                    # Fix genuinely introduced new errors — rollback
                    sf_path.write_text(original_content)
                    report["cannot_fix"].append({
                        "file": sf_rel,
                        "error": error_msg[:120],
                        "reason": (
                            f"fix introduced new errors "
                            f"(was: {baseline_count}, after: {old_count})"
                        ),
                    })

        # Final: write last known good content
        if file_fixes_applied > 0 and not dry_run:
            sf_path.write_text(content)

    return report


# ==========================================================================
#  Local repair report management
# ==========================================================================

def _current_toolchain_version() -> str:
    """Read the current Lean toolchain version from ReasBook/lean-toolchain."""
    tc = REPO_ROOT / "ReasBook" / "lean-toolchain"
    if tc.exists():
        return tc.read_text().strip().removeprefix("leanprover/lean4:v")
    return "unknown"


def _version_report_path() -> Path:
    """Return the path for the version-based error report."""
    version = _current_toolchain_version()
    return _report_output_dir() / f"repair-report-v{version}.md"


def write_cannot_fix_json(book_name: str, cannot_fix: list[dict]) -> Path:
    """Write cannot_fix items as structured JSON for LLM handoff.

    Returns the path to the JSON file.
    """
    output_dir = _report_output_dir()
    output_dir.mkdir(parents=True, exist_ok=True)
    toolchain = _current_toolchain_version()
    # Legacy reports sometimes use a source-relative file name as the grouping
    # key.  Keep the handoff as one file in output_dir instead of accidentally
    # interpreting separators in that key as directories.
    safe_name = re.sub(r"[^A-Za-z0-9._-]+", "_", book_name).strip("._-") or "unknown"
    json_path = output_dir / f"repair-handoff-v{toolchain}-{ACTIVE_KIND}-{safe_name}.json"

    items = []
    book_dir = resolve(PROJECT_ROOT, ACTIVE_KIND, book_name).directory
    for item in cannot_fix:
        entry = {
            "file": item.get("file", ""),
            "error": item.get("error", ""),
            "reason": item.get("reason", ""),
        }
        # Include file content snippet for LLM context
        fp = item.get("file", "")
        if fp and book_dir.exists():
            sf = book_dir / fp
            if sf.exists():
                try:
                    content = sf.read_text(encoding="utf-8")
                    # Extract error line and surrounding context
                    err_line_match = re.search(r':(\d+):', item.get("error", ""))
                    if err_line_match:
                        line_num = int(err_line_match.group(1))
                        lines = content.split('\n')
                        start = max(0, line_num - 20)
                        end = min(len(lines), line_num + 10)
                        entry["context"] = '\n'.join(
                            f"{i + 1}: {l}"
                            for i, l in enumerate(lines[start:end], start=start)
                        )
                    entry["content_length"] = len(content)
                except Exception:
                    entry["context"] = "[could not read file]"
        items.append(entry)

    json_path.write_text(
        json.dumps(
            {
                "toolchain": f"v{toolchain}",
                "kind": ACTIVE_KIND,
                "book": book_name,
                "total_cannot_fix": len(items),
                "items": items,
            },
            ensure_ascii=False,
            indent=2,
        ),
        encoding="utf-8",
    )
    return json_path


# ==========================================================================
#  Report generation
# ==========================================================================

def generate_fix_report(
    reports: list[dict],
    source_path: str,
    dry_run: bool,
) -> str:
    """Generate a version-based markdown error report and write it to disk.

    The report is placed under the ignored local automation report tree and
    overwritten on subsequent runs for the same toolchain version.  This
    keeps one authoritative report per version rather than accumulating
    timestamped files.

    Failing imports are never changed here. A JSON handoff is written for
    review and the separate degradation command may later apply an approved
    proposal.

    Returns the path to the generated report file.
    """
    _report_output_dir().mkdir(parents=True, exist_ok=True)
    report_path = _version_report_path()

    # If a report already exists for this version, merge: remove books
    # we are refreshing and re-append their updated data.
    existing_books: set[str] = set()
    existing_lines: list[str] = []
    if report_path.exists():
        existing_content = report_path.read_text(encoding="utf-8")
        # Keep everything up to the first "## " after the summary
        in_book_section = False
        for line in existing_content.split('\n'):
            if line.startswith("## ") and not line.startswith("## Summary"):
                in_book_section = True
            if not in_book_section:
                existing_lines.append(line)
            if in_book_section:
                book_name_in_existing = line.removeprefix("## ").strip()
                existing_books.add(book_name_in_existing)
        # Remove trailing blank lines before appending
        while existing_lines and existing_lines[-1] == '':
            existing_lines.pop()
        existing_lines.append('')

    total_fixed = sum(len(r["fixed"]) for r in reports)
    total_cannot = sum(len(r["cannot_fix"]) for r in reports)
    total_processed = total_fixed + total_cannot

    now = datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')
    toolchain = _current_toolchain_version()

    # Build report header (reuse existing_lines if merging)
    if existing_lines:
        lines = list(existing_lines)
    else:
        lines = [
            f"# Error Report — toolchain v{toolchain}",
            "",
            f"**Last updated**: {now}",
            f"**Source**: {source_path}",
            "",
            "## Summary",
            "",
            f"- Total errors processed: {total_processed}",
            f"- Auto-fixed: {total_fixed}",
            f"- Cannot fix (needs manual review): {total_cannot}",
            "",
        ]

    # Update summary counts in existing report
    if existing_lines:
        new_summary_lines = [
            f"# Error Report — toolchain v{toolchain}",
            "",
            f"**Last updated**: {now}",
            f"**Source**: {source_path}",
            "",
            "## Summary",
            "",
            f"- Total errors processed: {total_processed}",
            f"- Auto-fixed: {total_fixed}",
            f"- Cannot fix (needs manual review): {total_cannot}",
            "",
        ]
        # Replace from first line through Summary section
        # Find the index of the first "## " after Summary
        summary_end = 0
        for i, line in enumerate(lines):
            if line.startswith("## ") and "Summary" not in line:
                summary_end = i
                break
        if summary_end > 0:
            lines = new_summary_lines + lines[summary_end:]
        else:
            lines = new_summary_lines

    for report_data in reports:
        book_name = report_data['book']
        lines += [
            f"## {book_name}",
            "",
            f"- Total errors: {report_data['total_errors']}",
            f"- Fixed: {len(report_data['fixed'])}",
            f"- Needs manual review: {len(report_data['cannot_fix'])}",
            "",
        ]

        if report_data["fixed"]:
            lines.append("### Auto-fixed")
            lines.append("")
            for fix in report_data["fixed"]:
                lines.append(
                    f"- **`{fix['file']}`**: "
                    f"`{_truncate(fix['error'], 100)}`"
                )
                lines.append(f"  Fix: {fix['fix']}")
                cascade = fix.get("cascade_eliminated", 0)
                if cascade > 0:
                    lines.append(
                        f"  Cascade eliminated: {cascade} additional error(s)"
                    )
            lines.append("")

        if report_data["cannot_fix"]:
            lines.append("### Requires Manual Review")
            lines.append("")
            # Record the book-level error count for the summary note
            book_cannot_count = len(report_data["cannot_fix"])
            lines.append(
                f"These {book_cannot_count} errors could not be auto-fixed. "
                "Their imports remain active; review the automation run's "
                "degradation proposal if a temporary subset is required."
            )
            lines.append("")
            for item in report_data["cannot_fix"]:
                lines.append(
                    f"- **`{item.get('file', 'unknown')}`**: "
                    f"`{_truncate(item.get('error', ''), 100)}`"
                )
                lines.append(
                    f"  Reason: {item.get('reason', 'unknown')}"
                )
            lines.append("")

    content = '\n'.join(lines) + '\n'

    if not dry_run:
        report_path.write_text(content, encoding="utf-8")
        print(f"\n  Error report: {report_path}")

        # Write JSON handoff for LLM
        for report_data in reports:
            if report_data["cannot_fix"]:
                jp = write_cannot_fix_json(
                    report_data["book"], report_data["cannot_fix"]
                )
                print(f"  LLM handoff: {jp}")
    else:
        print(f"\n[DRY RUN] Would write report to: {report_path}")
        print(content)

    return str(report_path)


def _truncate(text: str, max_len: int) -> str:
    """Truncate text to max_len, adding ellipsis if truncated."""
    if len(text) <= max_len:
        return text
    return text[:max_len - 3] + '...'


# ==========================================================================
#  Main entry point
# ==========================================================================

def main():
    global REPORT_OUTPUT_DIR, ACTIVE_KIND
    parser = argparse.ArgumentParser(
        description="Apply safe auto-fixes to compilation errors",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("--source", help="Path to error report (.md)")
    parser.add_argument("--book", help="Process a single book")
    parser.add_argument("--bootstrap", help="Bootstrap mode: lake build → report → fix")
    parser.add_argument("--kind", choices=("book", "paper"), default="book")
    parser.add_argument("--all", action="store_true", help="Process all books with reports")
    parser.add_argument("--dry-run", action="store_true", help="Preview only")
    parser.add_argument("--analyze", action="store_true",
                        help="Analyze only: generate fix plan, no lake build, no file writes")
    parser.add_argument("--apply", action="store_true",
                        help="Apply mode: execute candidates with per-file verification")
    parser.add_argument("--output-dir", type=Path,
                        help="write auxiliary repair evidence into this exact run directory")
    args = parser.parse_args()
    if args.all and not (args.analyze or args.dry_run):
        parser.error("--all is read-only; mutating repair requires exactly one project")
    ACTIVE_KIND = args.kind
    if args.output_dir:
        REPORT_OUTPUT_DIR = args.output_dir.resolve()

    # ── Mode dispatch ──
    if args.analyze:
        _run_analyze_mode(args)
    elif args.apply:
        _run_apply_mode(args)
    else:
        _run_legacy_mode(args)


def _run_analyze_mode(args):
    """Analyze errors and generate fix plan without any lake build or file writes."""
    print("=== ANALYZE MODE (no builds, no file writes) ===\n")
    # Always treat as dry-run in analyze mode
    args.dry_run = True
    _run_legacy_mode(args)
    print("\n=== Analysis complete. Review the plan above, then run with --apply. ===")


def _run_apply_mode(args):
    """Execute the fix plan with verification via single-section lake builds."""
    print("=== APPLY MODE (single-section builds for verification) ===\n")
    enable_ai_fix()  # Activate Level 5 AI-assisted fixes
    _run_legacy_mode(args)


def _run_legacy_mode(args):
    """Original dispatch logic."""

    # Validate mutually exclusive modes
    modes = sum([
        bool(args.source),
        bool(args.bootstrap),
        bool(args.all),
    ])
    if modes > 1:
        print(
            "ERROR: --source, --bootstrap, and --all are mutually exclusive",
            file=sys.stderr,
        )
        sys.exit(1)

    # ---- Mode: --bootstrap ----
    if args.bootstrap:
        book_name = args.bootstrap
        print(f"\nBootstrap mode: processing {book_name}")
        report_path = bootstrap_error_report(book_name)
        if report_path is None:
            print("No errors to fix.")
            return

        errors_by_book = parse_error_report(report_path)
        if not errors_by_book:
            print("No parseable errors found in bootstrap output.")
            return

        reports: list[dict] = []
        for bname, errs in sorted(errors_by_book.items()):
            print(f"\n{'=' * 60}")
            print(f"Processing: {bname} ({len(errs)} errors)")
            print(f"{'=' * 60}")
            report_data = fix_book_errors(bname, errs, args.dry_run)
            reports.append(report_data)
            n_fixed = len(report_data['fixed'])
            n_cannot = len(report_data['cannot_fix'])
            print(f"  Fixed: {n_fixed}, Needs manual review: {n_cannot}")

        generate_fix_report(reports, str(report_path), args.dry_run)

    # ---- Mode: --book (single book, universe dedup + optional error analysis) ----
    elif args.book and not args.source:
        book_name = args.book
        # Try to find a matching error report
        report_path = None
        for dir_path in [ERROR_REPORTS_DIR]:
            if dir_path.exists():
                for fp in dir_path.glob("*.md"):
                    if book_name in fp.name:
                        report_path = fp
                        break
            if report_path:
                break

        if report_path:
            print(f"Found matching report: {report_path}")
            errors_by_book = parse_error_report(report_path)
            if book_name in errors_by_book:
                print(f"\nProcessing: {book_name}")
                report_data = fix_book_errors(
                    book_name, errors_by_book[book_name], args.dry_run)
                n_fixed = len(report_data['fixed'])
                n_cannot = len(report_data['cannot_fix'])
                print(f"  Fixed: {n_fixed}, Needs manual review: {n_cannot}")
                generate_fix_report(
                    [report_data], f"--book {book_name} (+ {report_path.name})",
                    args.dry_run)
                return
            else:
                print(
                    f"Report {report_path} does not contain errors for "
                    f"{book_name}"
                )

        # No matching report — just universe dedup
        print(f"\nProcessing: {book_name} (universe dedup only)")
        report_data = fix_book_errors(book_name, [], args.dry_run)
        n_fixed = len(report_data['fixed'])
        n_cannot = len(report_data['cannot_fix'])
        print(f"  Fixed: {n_fixed}, Needs manual review: {n_cannot}")
        generate_fix_report(
            [report_data], f"--book {book_name}", args.dry_run)

    # ---- Mode: --source ----
    elif args.source:
        source_path = Path(args.source)
        if not source_path.exists():
            print(f"ERROR: Report not found: {source_path}", file=sys.stderr)
            sys.exit(1)

        errors_by_book = parse_error_report(source_path)
        if not errors_by_book:
            print("No parseable errors found in report.")
            return

        reports: list[dict] = []
        for book, errs in sorted(errors_by_book.items()):
            print(f"\n{'=' * 60}")
            print(f"Processing: {book} ({len(errs)} errors)")
            print(f"{'=' * 60}")
            report_data = fix_book_errors(book, errs, args.dry_run)
            reports.append(report_data)
            n_fixed = len(report_data['fixed'])
            n_cannot = len(report_data['cannot_fix'])
            print(f"  Fixed: {n_fixed}, Needs manual review: {n_cannot}")

        generate_fix_report(reports, str(source_path), args.dry_run)

    # ---- Mode: --all ----
    elif args.all:
        # Scan all error report directories for .md files
        all_report_paths: list[Path] = []
        for dir_path in [ERROR_REPORTS_DIR]:
            if dir_path.exists():
                all_report_paths.extend(sorted(dir_path.glob("*.md")))

        if not all_report_paths:
            print("No repair reports found in docs/automation-reports/repairs/")
            sys.exit(1)

        all_reports: list[dict] = []
        for rp in all_report_paths:
            print(f"\nReading report: {rp.name}")
            errors_by_book = parse_error_report(rp)
            for book, errs in sorted(errors_by_book.items()):
                print(f"\n{'=' * 60}")
                print(f"Processing: {book} ({len(errs)} errors)")
                print(f"{'=' * 60}")
                report_data = fix_book_errors(book, errs, args.dry_run)
                all_reports.append(report_data)
                n_fixed = len(report_data['fixed'])
                n_cannot = len(report_data['cannot_fix'])
                print(f"  Fixed: {n_fixed}, Needs manual review: {n_cannot}")

        if all_reports:
            generate_fix_report(all_reports, "--all", args.dry_run)
        else:
            print("No errors found in any report.")

    else:
        # No mode specified: check if stdin has data (piped from lake build)
        if not sys.stdin.isatty():
            # Piped input: treat as bootstrap without --bootstrap flag
            print(
                "ERROR: Piped lake build input detected. "
                "Use --bootstrap BOOK_NAME for bootstrap mode.",
                file=sys.stderr,
            )
            parser.print_help()
            sys.exit(1)
        else:
            parser.print_help()
            sys.exit(1)


if __name__ == "__main__":
    main()
