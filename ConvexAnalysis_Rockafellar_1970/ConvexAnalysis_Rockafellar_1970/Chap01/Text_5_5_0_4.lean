import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_5_3

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Text 5.5.0.4 considers on `ℝ^n` the map
  `x ↦ max { |x j| | j = 1, ..., n }`; the canonical finite-coordinate owner layer is an
  arbitrary finite index type `ι`, and the reused norm owner already works on finite families in
  any real seminormed coordinate spaces `G i`.
- `core/canonical`: the owner theorem is already upstream as `Function.isConvex_norm`, stating
  global convexity of the norm as a `WithTopBot ℝ`-valued function.
- `bridge/view`: specialize that owner to a dependent finite product `((i : ι) → G i)`, then
  rewrite with `Pi.norm_def'` to get the finite-coordinate supremum expression.
- Primitive data vs derived API: no new owner is introduced here; this file provides only the
  finite-coordinate bridge statements of the existing canonical owner.
- Domain-style sampling used here: `Function.isConvex_norm`, `Pi.norm_def'`.
- Layer target: keep the public owner at `Function.isConvex_norm`; keep this item at the abstract
  finite-index bridge layer and leave concrete `ℝ^n` formulas to downstream specialization.
-/

/- Text 5.5.0.4 uses the canonical owner theorem `Function.isConvex_norm`; no parallel local
owner is introduced in this file. -/
recall Function.isConvex_norm

section

variable {ι : Type*} [Fintype ι]
variable {G : ι → Type*}
variable [∀ i, SeminormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]

/-- Coordinate bridge form of Text 5.5.0.4: on any finite coordinate family of real seminormed
spaces, the coordinate-supremum expression for the norm is globally convex. -/
theorem Function.isConvex_pi_univSup_nnnorm :
    ((fun x : (i : ι) → G i ↦
      ((Finset.univ.sup fun j : ι ↦ ‖x j‖₊ : NNReal) : ℝ)).toWithTopBot).IsConvex ℝ := by
  simpa [Pi.norm_def'] using (Function.isConvex_norm (E := (i : ι) → G i))

end
