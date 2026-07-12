import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

/-!
Source/core/bridge triage:
- `source-facing`: Text 18.0.1 says the empty set is a face of any set.
- `core/canonical`: the chapter owner is `Set.IsFace`; the source sentence is exactly
  `Set.IsFace.empty`.
- `bridge/view`: no extra bridge theorem is needed, since this is already an owner theorem.

Abstraction checks:
- codomain/ambient layer: no ordered-extended codomain is involved.
- scalar/ambient minimization: the reused owner theorem is already at the weak primitive layer
  `[Semiring R] [PartialOrder R] [SMul R E]`, not a concrete `ℝ`/module specialization.
- owner correctness: `Set.IsFace` is the intrinsic chapter owner; no concrete-model wrapper appears.
- topology phrasing: this item has no ambient-vs-relative topological content.
- notation surface: expose both the owner-facing statement and the textbook face-family surface
  `(∅ : Set E) ∈ 𝓕[R](C)` through owner theorem `Set.IsFace.empty_mem_faces`.
-/

/-- Text 18.0.1 (notation form): the empty set belongs to every face family. -/
recall Set.IsFace.empty_mem_faces

/-- Text 18.0.1: the empty set is a face of any set.

This source statement is exposed at the intrinsic set-theoretic surface `∅`. -/
recall Set.IsFace.empty
