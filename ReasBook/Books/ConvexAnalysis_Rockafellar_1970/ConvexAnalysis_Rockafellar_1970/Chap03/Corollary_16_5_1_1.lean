import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar
open Function

universe u v w

section ConvexIndicatorBridge

variable {𝕜 : Type*} {X : Type u}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]

omit [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜] in
private theorem convex_minorant_indicator_le_indicator_convexHull
    (S : Set X) {g : X → WithBotTop 𝕜} (hg_convex : g.IsConvex 𝕜)
    (hg_le : g ≤ (δ[𝕜](· | S))) :
    g ≤ (δ[𝕜](· | convexHull 𝕜 S)) := by
  intro x
  by_cases hx : x ∈ convexHull 𝕜 S
  · have hsubset_epi : (LinearMap.inl 𝕜 X 𝕜) '' S ⊆ epi g := by
      intro p hp
      rcases hp with ⟨s, hs, rfl⟩
      rw [mem_epi_iff]
      exact (hg_le s).trans (by simp [hs])
    have hconv_epi : Convex 𝕜 (epi g) := hg_convex.convex_epi
    have hconvHull_subset :
        convexHull 𝕜 ((LinearMap.inl 𝕜 X 𝕜) '' S) ⊆ epi g :=
      convexHull_min hsubset_epi hconv_epi
    have himage :
        (LinearMap.inl 𝕜 X 𝕜) '' convexHull 𝕜 S =
          convexHull 𝕜 ((LinearMap.inl 𝕜 X 𝕜) '' S) := by
      simpa using (LinearMap.image_convexHull (f := LinearMap.inl 𝕜 X 𝕜) (s := S))
    have hx_image : (x, (0 : 𝕜)) ∈ convexHull 𝕜 ((LinearMap.inl 𝕜 X 𝕜) '' S) := by
      have hx' : (x, (0 : 𝕜)) ∈ (LinearMap.inl 𝕜 X 𝕜) '' convexHull 𝕜 S :=
        ⟨x, hx, rfl⟩
      exact himage ▸ hx'
    have hx_epi : (x, (0 : 𝕜)) ∈ epi g := hconvHull_subset hx_image
    have hx_le_zero : g x ≤ (0 : 𝕜) := by
      simpa [mem_epi_iff] using hx_epi
    simpa [hx] using hx_le_zero
  · simp [hx]

omit [DenselyOrdered 𝕜] in
private theorem convexHullFunction_indicatorFunction_eq_indicatorFunction_convexHull
    (S : Set X) :
    conv((δ[𝕜](· | S))) = (δ[𝕜](· | convexHull 𝕜 S)) := by
  let f : Unit → X → WithBotTop 𝕜 := fun _ ↦ (δ[𝕜](· | S))
  let hHull := Function.isGreatest_conv_iInf_minorant f
  have hminor : conv((δ[𝕜](· | S))) ≤ (δ[𝕜](· | S)) := by
    simpa [f] using hHull.1.2
  have hconvex : (conv((δ[𝕜](· | S)))).IsConvex 𝕜 := by
    simpa [f] using hHull.1.1
  have hindicator_convex : ((δ[𝕜](· | convexHull 𝕜 S))).IsConvex 𝕜 :=
    (indicator_isConvex_iff (C := convexHull 𝕜 S)).2 (convex_convexHull 𝕜 S)
  have hindicator_minor :
      (δ[𝕜](· | convexHull 𝕜 S)) ≤ (δ[𝕜](· | S)) := by
    intro x
    by_cases hxS : x ∈ S
    · have hxh : x ∈ convexHull 𝕜 S := subset_convexHull 𝕜 S hxS
      simp [hxS, hxh]
    · by_cases hxh : x ∈ convexHull 𝕜 S
      · simp [hxS, hxh]
      · simp [hxS, hxh]
  have hind_le_conv :
      (δ[𝕜](· | convexHull 𝕜 S)) ≤ conv((δ[𝕜](· | S))) := by
    have hmem :
        (δ[𝕜](· | convexHull 𝕜 S)) ∈ Function.convexMinorants (⨅ i : Unit, f i) := by
      simpa [f] using
        (show (δ[𝕜](· | convexHull 𝕜 S)) ∈ Function.convexMinorants (δ[𝕜](· | S)) from
          ⟨hindicator_convex, hindicator_minor⟩)
    simpa [f] using hHull.2 hmem
  have hconv_le_hind :
      conv((δ[𝕜](· | S))) ≤ (δ[𝕜](· | convexHull 𝕜 S)) :=
    convex_minorant_indicator_le_indicator_convexHull S hconvex hminor
  exact le_antisymm hconv_le_hind hind_le_conv

end ConvexIndicatorBridge

section IndicatorIUnion

private theorem iInf_indicatorFunction_eq_indicatorFunction_iUnion
    {F : Type*} {𝕜 : Type*} [Zero 𝕜] [ConditionallyCompleteLattice 𝕜]
    {I : Sort w} (C : I → Set F) :
    (fun x : F ↦ ⨅ i : I, δ[𝕜](x | C i)) = (δ[𝕜](· | ⋃ i : I, C i)) := by
  funext x
  by_cases hx : x ∈ ⋃ i : I, C i
  · rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    rw [indicator_def, if_pos hx]
    apply le_antisymm
    · refine iInf_le_of_le i ?_
      simp [hi]
    · refine le_iInf fun j ↦ ?_
      by_cases hj : x ∈ C j
      · simp [hj]
      · simp [hj]
  · have hnot : ∀ i : I, x ∉ C i := by
      simpa [Set.mem_iUnion] using hx
    rw [indicator_def, if_neg hx]
    by_cases hI : Nonempty I
    · refine le_antisymm le_top ?_
      refine le_iInf fun j ↦ ?_
      simp [hnot j]
    · haveI : IsEmpty I := not_nonempty_iff.mp hI
      simp

end IndicatorIUnion

section

variable {𝕜 : Type*} {X : Type u} {Y : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [DenselyOrdered 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]
variable {I : Sort w}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.5.1.1 identifies the support function of
  `convexHull 𝕜 (⋃ i, C i)` with the pointwise supremum of the family support functions.
- `core/canonical`: `supportFunction`, `indicator`, `Function.convexHull`, and
  `convexConjugate_conv_iInf_eq_iSup`.
- `bridge/view`: rewrite support functions as conjugates of indicators by
  `convexConjugate_indicatorFunction_eq_supportFunction`, then apply Theorem 16.5.1.
-/

/-- Corollary 16.5.1.1 at the pairing layer: the support function of the convex hull of a union
is the pointwise supremum of the support functions of the members. -/
theorem supportFunction_convexHull_iUnion_eq_iSup_supportFunction
    (C : I → Set X) :
    (fun y : Y ↦ δᵛ[WithBotTop 𝕜](y | convexHull 𝕜 (⋃ i : I, C i))) =
      ⨆ i : I, (fun y : Y ↦ δᵛ[WithBotTop 𝕜](y | C i)) := by
  let f : I → X → WithBotTop 𝕜 := fun i ↦ (δ[𝕜](· | C i))
  calc
    (fun y : Y ↦ δᵛ[WithBotTop 𝕜](y | convexHull 𝕜 (⋃ i : I, C i)))
        = ((δ[𝕜](· | convexHull 𝕜 (⋃ i : I, C i)))⋆) := by
            simpa using
              (convexConjugate_indicatorFunction_eq_supportFunction
                (C := convexHull 𝕜 (⋃ i : I, C i))).symm
    _ = (conv((δ[𝕜](· | ⋃ i : I, C i))))⋆ := by
          rw [convexHullFunction_indicatorFunction_eq_indicatorFunction_convexHull]
    _ = (conv(⨅ i : I, f i))⋆ := by
          have hf : (δ[𝕜](· | ⋃ i : I, C i)) = ⨅ i : I, f i := by
            funext x
            simpa [f] using congrFun (iInf_indicatorFunction_eq_indicatorFunction_iUnion C).symm x
          rw [hf]
    _ = ⨆ i : I, (f i)⋆ :=
          convexConjugate_conv_iInf_eq_iSup f
    _ = ⨆ i : I, (fun y : Y ↦ δᵛ[WithBotTop 𝕜](y | C i)) := by
          ext y
          rw [iSup_apply, iSup_apply]
          congr with i
          simpa [f] using
            congrFun
              (convexConjugate_indicatorFunction_eq_supportFunction
                (C := C i)) y

end
