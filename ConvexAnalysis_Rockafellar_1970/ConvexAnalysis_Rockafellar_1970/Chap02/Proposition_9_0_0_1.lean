import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_6

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Proposition 9.0.0.1 contrasts two image behaviors: exact preservation of
  relative interior for convex sets under linear maps, and one-sided preservation of closure under
  continuous maps.
- `core/canonical`: both clauses already live upstream at the right owners:
  `Convex.intrinsicInterior_linear_image` and `image_closure_subset_closure_image`.
- `bridge/view`: Rockafellar's `ri (A C) = A (ri C)` and `cl (A C) ⊇ A (cl C)` are therefore kept
  as direct recalls of those canonical owners, instead of introducing local wrapper names.
- Primitive data vs derived API: this file introduces no new primitive notion, so adding duplicate
  theorem wrappers would only overgrow the public API.
- Layer target: recall-only item; no compatibility aliases for already-canonical owners.
- Abstraction checks:
  - codomain/ambient layer: no codomain owner is introduced here; both clauses reuse existing
    set-level canonical owners directly;
  - scalar/ambient assumptions: this file adds no local assumptions and therefore does not
    overconstrain any theorem surface;
  - owner choice: no concrete-model owner is introduced; the item reuses intrinsic owner APIs;
  - topology phrasing: the relative-interior clause is already intrinsic (`ri`), while the closure
    clause is the canonical ambient continuity theorem;
  - naming/notation: no long local owner names or wrapper notation are added.
-/

/- The relative-interior clause quoted in Proposition 9.0.0.1 is exactly Theorem 6.6 (1), namely
that a linear map sends the relative interior of a convex set onto the relative interior of its
image. -/
recall Convex.intrinsicInterior_linear_image

/- The closure clause quoted in Proposition 9.0.0.1 is exactly the canonical continuity theorem:
for a continuous map `A`, one has `A '' closure C ⊆ closure (A '' C)`, equivalently
`cl (A C) ⊇ A (cl C)`. -/
recall image_closure_subset_closure_image
