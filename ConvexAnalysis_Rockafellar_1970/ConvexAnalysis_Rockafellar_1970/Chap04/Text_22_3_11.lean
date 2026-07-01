import Mathlib.Tactic.Recall
import Mathlib.Algebra.Group.Support

-- Declarations for this item will be appended below by the statement pipeline.

open Function

/-!
Source/core/bridge triage:
- `source-facing`: Text 22.3.11 introduces support as the index set of nonzero coordinates of a
  coordinate function.
- `core/canonical`: the existing mathlib owner is `support` for functions into a type
  with zero; concrete coordinate models are only downstream specializations.
- `bridge/view`: the textbook display `{j | ζ_j ≠ 0}` is exactly the membership
  predicate given by `mem_support`.
- Domain-style sampling used here: `support`, `mem_support`, and
  `support_subset_iff`.
- Layer target: `bridge/view`, so this item should be a direct canonical recall rather than a new
  local wrapper around the same support notion.
- Abstraction checks:
  - codomain/ambient layer: only `[Zero M]` is needed; no scalar, order, or topology structure.
  - owner layer: intrinsic owner `support` is already the canonical layer.
  - topology language: no ambient/intrinsic topology owner appears in this item.
-/

/- Text 22.3.11: the support of a coordinate function is the canonical set
`support z` of indices whose coordinates are nonzero. -/
recall support

/- Membership in the support is exactly the coordinatewise nonvanishing condition. -/
recall mem_support

/- The primitive support-inclusion owner uses the direct nonzero-membership formulation. -/
recall support_subset_iff

/- Textbook bridge form: support inclusion is equivalent to vanishing outside the containing
index set. -/
recall support_subset_iff'
