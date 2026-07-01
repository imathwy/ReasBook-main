import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

/-!
Source/core/bridge triage:
- `source-facing`: the item states that a convex set is a face of itself.
- `core/canonical`: the source-facing owner is `Set.IsFace`, with reflexivity theorem
  `Set.IsFace.refl`.
- `bridge/view`: for textbook face-family notation, use the canonical bridge theorem
  `Set.IsFace.mem_faces_self` from `Defn_18_1`.

Abstraction checks:
- codomain/ambient layer: no ordered extended codomain is involved in this item;
  the statement only concerns face ownership on sets.
- scalar/ambient minimization: the reused owner theorem already lives over the weak
  `[Semiring R] [PartialOrder R] [SMul R E]` layer from `Defn_18_1`, not a concrete
  real-scalar/module specialization.
- owner correctness: `Set.IsFace` is the intrinsic chapter owner for faces; no concrete-model
  wrapper is present.
- topology phrasing: this item has no topological content, so there is no ambient-vs-relative
  topology choice to normalize.
- notation surface: the source-facing API is exposed both in owner form (`C.IsFace R C`) and
  in textbook face-family notation form `C ∈ 𝓕[R](C)` through the canonical bridge theorem
  `Set.IsFace.mem_faces_self`.

Domain-style sampling used here:
- `Set.IsFace`;
- `𝓕[R](C) = Set.IsFace.faces R C`;
- `Set.IsFace.mem_faces_iff`;
- `Set.IsFace.mem_faces_self`;
- `Set.IsFace.refl`;
- `Convex`.
-/

/- Text 18.0.2 (notation form): every convex set belongs to its own face family. -/
recall Set.IsFace.mem_faces_self

/- Text 18.0.2: every convex set is a face of itself. This is exactly the owner theorem
`Set.IsFace.refl`. -/
recall Set.IsFace.refl
