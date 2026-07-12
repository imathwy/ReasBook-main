import Mathlib.Analysis.Convex.Exposed
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:
- `source-facing`: the text says that every exposed point of a convex set is an extreme point.
- `core/canonical`: mathlib's owner abstractions are `Set.exposedPoints` and
  `Set.extremePoints`.
- `bridge/view`: the source sentence is exactly the canonical subset theorem
  `exposedPoints_subset_extremePoints`.
- Primitive data vs derived API: this item introduces no new data; it records a direct consequence
  between two existing canonical point sets.
- Domain-style sampling used here: `Set.exposedPoints`,
  `mem_exposedPoints_iff_exposed_singleton`, `IsExposed.isExtreme`, and
  `exposedPoints_subset_extremePoints`.
- Layer target: `core/canonical`, by direct recall of the existing owner theorem.

Abstraction checks:
- codomain/ambient layer: this item has no ordered-extended function codomain surface.
- scalar/ambient minimization: the canonical theorem already carries the needed scalar/topological
  layer and is not a concrete model specialization.
- owner correctness: `Set.exposedPoints` and `Set.extremePoints` are the intrinsic owners.
- topology phrasing: this item is not an ambient-vs-relative topology statement.
- notation surface: the owner-level set inclusion is already the canonical theorem surface.
-/

/- Text 18.0.8: every exposed point of a convex set is an extreme point. The canonical theorem
`exposedPoints_subset_extremePoints` is strictly stronger, since it is stated for an arbitrary set
(with no convexity hypothesis). -/
recall exposedPoints_subset_extremePoints
