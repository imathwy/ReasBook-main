import «stacks_project».Chap25.«25_11_0_3»

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace

noncomputable section

universe u v w

/- Source/core/bridge triage:
- `source-facing`: the pairwise intersection condition on the level-`0` and level-`1` opens;
- `core/canonical`: the generic Chapter 25 owner `HypercoveringIntersectionCondition`;
- `bridge/view`: the `n = 0` specialization from a pair of face maps `d0, d1`.

This file keeps the source-facing two-index interface as a thin bridge to that canonical owner. -/

variable {X : TopCat.{u}} {I0 : Type v} {I1 : Type w}

/-- 25.11.0.2: for every pair `i0, i1 : I0`, the intersection `U0 i0 ∩ U0 i1` is covered by the
level-`1` opens whose two face maps are `i0` and `i1`. This is the source-facing `n = 0`
specialization of `HypercoveringIntersectionCondition`. -/
@[stacks 01H3]
abbrev HypercoveringPairwiseIntersectionCondition
    (d0 d1 : I1 → I0) (U0 : I0 → Opens X) (U1 : I1 → Opens X) : Prop :=
  HypercoveringIntersectionCondition ![d0, d1] U0 U1

namespace HypercoveringPairwiseIntersectionCondition

/-- Unfolding `HypercoveringPairwiseIntersectionCondition` at a chosen pair of `0`-simplices gives
the corresponding covering equality of opens. -/
theorem inf_eq_iSup
    {d0 d1 : I1 → I0} {U0 : I0 → Opens X} {U1 : I1 → Opens X}
    (h : HypercoveringPairwiseIntersectionCondition d0 d1 U0 U1)
    (i0 i1 : I0) :
    U0 i0 ⊓ U0 i1 =
      iSup (fun i : { i : I1 // d0 i = i0 ∧ d1 i = i1 } ↦ U1 i.1) := by
  have hinf : U0 i0 ⊓ U0 i1 = ⨅ a, U0 (![i0, i1] a) := by
    apply le_antisymm
    · refine le_iInf ?_
      intro a
      fin_cases a
      · exact inf_le_left
      · exact inf_le_right
    · exact le_inf (iInf_le _ 0) (iInf_le _ 1)
  have hiSup :
      iSup (fun i : HypercoveringMatchingIndices ![d0, d1] ![i0, i1] ↦ U1 i.1) =
        iSup (fun i : { i : I1 // d0 i = i0 ∧ d1 i = i1 } ↦ U1 i.1) := by
    refine Equiv.iSup_congr (HypercoveringMatchingIndices.finTwoEquiv d0 d1 i0 i1) ?_
    intro i
    simp
  calc
    U0 i0 ⊓ U0 i1 = ⨅ a, U0 (![i0, i1] a) := hinf
    _ = iSup (fun i : HypercoveringMatchingIndices ![d0, d1] ![i0, i1] ↦ U1 i.1) :=
      h.iInf_eq_iSup ![i0, i1]
    _ = iSup (fun i : { i : I1 // d0 i = i0 ∧ d1 i = i1 } ↦ U1 i.1) := hiSup

end HypercoveringPairwiseIntersectionCondition
