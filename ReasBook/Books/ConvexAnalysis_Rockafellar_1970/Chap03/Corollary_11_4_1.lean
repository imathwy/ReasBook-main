import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_9_1_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_11_4

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Pointwise Rockafellar
open Set

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [HasLinearPairing E Y 𝕜]
/-!
Source/core/bridge triage:

- `core/canonical`: the primitive Chapter 11 owner bridge is
  `exists_hyperplane_strongly_separating_iff_zero_notMem_closure_sub`.
  At this layer, the essential extra input is closedness of `C1 - C2`.
- `source-facing`: Corollary 11.4.1 adds the textbook common-recession hypothesis as a sufficient
  condition implying that closedness.
- `bridge/view`: this file keeps both layers explicitly:
  1) a primitive owner theorem from `Disjoint + IsClosed (C1 - C2)`, then
  2) a source-facing corollary deriving `IsClosed (C1 - C2)` by rewriting as `C1 + (-C2)` and
     using the Chapter 2 closed-sum owner.
-/

/-- Primitive separation bridge on the Chapter 11 owner layer: for nonempty convex sets, disjoint
sets with closed difference admit a strongly separating hyperplane. -/
theorem exists_hyperplane_strongly_separating_of_disjoint_convex_of_isClosed_sub
    {C1 C2 : Set E} (hC1_nonempty : C1.Nonempty) (hC1_convex : Convex 𝕜 C1)
    (hC2_nonempty : C2.Nonempty) (hC2_convex : Convex 𝕜 C2) (hdisj : Disjoint C1 C2)
    (hsub_closed : IsClosed (C1 - C2)) :
    ∃ H : AffineSubspace 𝕜 E, H stronglySeparates[Y] C1 and C2 := by
  have hzero_notMem_sub : (0 : E) ∉ C1 - C2 := by
    intro h0
    rcases Set.mem_sub.mp h0 with ⟨x1, hx1, x2, hx2, hsub⟩
    exact hdisj.le_bot ⟨hx1, by simpa [sub_eq_zero.mp hsub] using hx2⟩
  have hsep_iff :
      (∃ H : AffineSubspace 𝕜 E, H stronglySeparates[Y] C1 and C2) ↔
        (0 : E) ∉ closure (C1 - C2) :=
    exists_hyperplane_strongly_separating_iff_zero_notMem_closure_sub
      hC1_convex hC1_nonempty hC2_convex hC2_nonempty
  exact hsep_iff.mpr (by simpa [hsub_closed.closure_eq] using hzero_notMem_sub)

end

section

open scoped Pointwise Rockafellar
open Set

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [HasLinearPairing E Y 𝕜]

/-- Corollary 11.4.1: if `C1` and `C2` are nonempty disjoint closed convex sets and
`C1 ⟂₀⁺[𝕜] (-C2)`, then some hyperplane strongly separates `C1` and `C2`.
This owner condition is equivalent to saying that every common recession direction of
`C1` and `C2` is zero. -/
-- Proof sketch: derive `IsClosed (C1 - C2)` from `C1 ⟂₀⁺[𝕜] (-C2)` by rewriting
-- `C1 - C2` as `C1 + (-C2)` and applying the Chapter 2 closed-sum owner. Then invoke the
-- primitive separation bridge
-- `exists_hyperplane_strongly_separating_of_disjoint_convex_of_isClosed_sub`.
theorem
    exists_hyperplane_strongly_separating_of_disjoint_convex_of_no_common_recession_directions
    {C1 C2 : Set E} (hC1_nonempty : C1.Nonempty) (hC1_closed : IsClosed C1)
    (hC1_convex : Convex 𝕜 C1) (hC2_nonempty : C2.Nonempty) (hC2_closed : IsClosed C2)
    (hC2_convex : Convex 𝕜 C2) (hdisj : Disjoint C1 C2)
    (hno_common : C1 ⟂₀⁺[𝕜] (-C2)) :
    ∃ H : AffineSubspace 𝕜 E, H stronglySeparates[Y] C1 and C2 := by
  have hclosed_sub : IsClosed (C1 - C2) := by
    have hneg_closed : IsClosed (-C2) := by
      simpa [Set.mem_neg] using hC2_closed.preimage continuous_neg
    have hneg_convex : Convex 𝕜 (-C2) := by
      simpa using hC2_convex.neg
    have hclosed_add : IsClosed (C1 + (-C2)) :=
      hno_common.isClosed_add hC1_closed hneg_closed hC1_convex hneg_convex
    simpa [sub_eq_add_neg] using hclosed_add
  exact
    exists_hyperplane_strongly_separating_of_disjoint_convex_of_isClosed_sub
      hC1_nonempty hC1_convex hC2_nonempty hC2_convex hdisj hclosed_sub

end
