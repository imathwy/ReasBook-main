import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_1

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousConstSMul ℝ E] [FiniteDimensional ℝ E]

noncomputable local instance : SMul ℝ (WithTopBot ℝ) where
  smul r x := (r : WithTopBot ℝ) * x

open scoped Rockafellar
open Set

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 10.1.1 says that a finite convex function on `R^n`, hence an
  ordinary real-valued convex function on all of `R^n`, is continuous. As elsewhere in the chapter,
  the textbook `R^n` ambient space is rendered by the intrinsic owner layer of arbitrary
  finite-dimensional real topological vector spaces.
- `core/canonical`: the owner abstractions are mathlib's `ConvexOn ℝ (univ : Set E) f`,
  `ConvexOn.continuousOn`, and the whole-space bridge `continuousOn_univ`.
- `bridge/view`: the codomain owner layer is `WithTopBot ℝ`, with `EReal` used downstream only as
  notation/view. The whole-space finiteness owner is `dom(f) = univ`, while the specialization of
  Theorem 10.1 still takes the primitive bridge input `univ ⊆ dom(f)`.

Domain-style sampling used here:
- `ConvexOn.continuousOn`;
- `ConvexOn.locallyLipschitz`;
- `continuousOn_univ`;
- the chapter continuity theorem `Function.continuousOn_of_convexOn_univ`.

Primitive data vs derived API:
- primitive input: a real-valued function `f : E → ℝ` together with its global convexity owner
  `ConvexOn ℝ (univ : Set E) f`;
- derived API: global continuity `Continuous f`, obtained directly from the owner theorem
  `ConvexOn.continuousOn` and `continuousOn_univ`, so no parallel local theorem is kept;
- bridge API: continuity of a `WithTopBot ℝ`-valued convex function from the canonical full-domain
  owner hypothesis `dom(f) = univ`; the primitive Theorem 10.1 input `univ ⊆ dom(f)` is used only
  as an internal proof bridge. The pointwise real-valued condition is a downstream source-facing
  corollary.

Layer target: the real-valued content is `bridge/view`, handled by direct canonical recall of the
owner-side continuity declarations, while the extended-real theorem remains the nontrivial chapter
bridge.
-/

/- Corollary 10.1.1, real-valued owner form: for `f : E → ℝ`, whole-space continuity is obtained
directly from the canonical owner declarations `ConvexOn.continuousOn` and `continuousOn_univ`,
so no duplicate local theorem is introduced here. -/
recall ConvexOn.continuousOn
recall continuousOn_univ

namespace ConvexOn

-- Internal bridge: specialized Theorem 10.1 hypothesis shape at `C = univ`.
private theorem continuous_of_univ_subset_dom {f : E → WithTopBot ℝ}
    (hf : ConvexOn ℝ (univ : Set E) f)
    (hdom : (univ : Set E) ⊆ dom(f)) :
    Continuous f := by
  simpa [continuousOn_univ] using
    Function.continuousOn_of_convexOn_univ
      (f := f) hf isOpen_univ.isRelativelyOpen convex_univ hdom

/-- Canonical whole-domain owner form of Corollary 10.1.1:
if a convex `WithTopBot ℝ`-valued function has effective domain `univ`, then it is continuous. -/
theorem continuous_of_dom_eq_univ {f : E → WithTopBot ℝ}
    (hf : ConvexOn ℝ (univ : Set E) f)
    (hdom : dom(f) = (univ : Set E)) :
    Continuous f := by
  refine continuous_of_univ_subset_dom hf ?_
  intro x hx
  rw [hdom]
  exact hx

/-- Source-facing finite-valued corollary of Corollary 10.1.1:
if a convex `WithTopBot ℝ`-valued function is finite everywhere (equivalently, never `⊤`), then
it is continuous. -/
theorem continuous_of_finite {f : E → WithTopBot ℝ}
    (hf : ConvexOn ℝ (univ : Set E) f)
    (hf_finite : ∀ x : E, f x < ⊤) :
    Continuous f := by
  have hdom : dom(f) = (univ : Set E) := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      simpa [mem_effectiveDomain] using hf_finite x
  exact continuous_of_dom_eq_univ hf hdom

end ConvexOn

end
