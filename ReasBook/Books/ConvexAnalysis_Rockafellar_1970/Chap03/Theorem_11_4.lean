import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_0_3

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} {E : Type*} {Y : Type*}
variable [NormedField 𝕜] [LinearOrder 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]
variable {C1 C2 : Set E}

/-- Theorem 11.4 on the chapter's finite-dimensional normed pairing layer: for nonempty convex
sets `C1` and `C2`, there exists a hyperplane strongly separating them (in pairing codomain `Y`)
if and only if the origin does not belong to `closure (C1 - C2)`.

This file keeps the ambient closure formulation as the primary theorem surface, because the
criterion is about the ambient difference set `C1 - C2`; the positive-distance form is then a thin
restatement via `Metric.infDist_pos_iff_notMem_closure`. -/
-- Proof sketch: strong separation means that for some `ε > 0`, suitable closed-ball thickenings
-- of `C1` and `C2` lie in opposite open half-spaces. By the preceding separation criterion for
-- convex thickenings, this is equivalent to asking that `0` lie outside the pointwise
-- difference of those thickenings for some `ε > 0`. That difference is a `2 ε`-ball thickening
-- of `C1 - C2`, so the condition is exactly `0 ∉ closure (C1 - C2)`.
theorem exists_hyperplane_strongly_separating_iff_zero_notMem_closure_sub
    (hC1_conv : Convex 𝕜 C1) (hC1_nonempty : C1.Nonempty)
    (hC2_conv : Convex 𝕜 C2) (hC2_nonempty : C2.Nonempty) :
    (∃ H : AffineSubspace 𝕜 E, H stronglySeparates[Y] C1 and C2) ↔
      0 ∉ closure (C1 - C2) := sorry

/-- Theorem 11.4 in distance-to-set form: strong separation is equivalent to
`0 < Metric.infDist 0 (C1 - C2)`. -/
theorem exists_hyperplane_strongly_separating_iff_infDist_pos_sub
    (hC1_conv : Convex 𝕜 C1) (hC1_nonempty : C1.Nonempty)
    (hC2_conv : Convex 𝕜 C2) (hC2_nonempty : C2.Nonempty) :
    (∃ H : AffineSubspace 𝕜 E, H stronglySeparates[Y] C1 and C2) ↔
      0 < Metric.infDist 0 (C1 - C2) := by
  have hsub_nonempty : (C1 - C2).Nonempty := hC1_nonempty.sub hC2_nonempty
  rw [exists_hyperplane_strongly_separating_iff_zero_notMem_closure_sub
    hC1_conv hC1_nonempty hC2_conv hC2_nonempty]
  simpa using Metric.infDist_pos_iff_notMem_closure hsub_nonempty

end
