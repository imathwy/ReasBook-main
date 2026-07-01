/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
-/

import Mathlib
import Books.Analysis2_Tao_2022.Chapters.Chap06.section06_part1

section Chap06
section Section06

/-- Helper for Theorem 6.8: `S²` is connected as a topological space. -/
lemma helperForTheorem_6_8_connected_space_unitSphereTwo :
    ConnectedSpace UnitSphereTwo := by
  have hsphereConnected :
      IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    refine isConnected_sphere helperForTheorem_6_8_one_lt_rank_ambient
      (0 : EuclideanSpace ℝ (Fin 3)) ?_
    norm_num
  simpa [UnitSphereTwo] using (isConnected_iff_connectedSpace.1 hsphereConnected)

/-- Helper for Theorem 6.8: for any additive codomain, the map
`x ↦ g x - g (-x)` is odd on `S²`. -/
lemma helperForTheorem_6_8_odd_sub_antipode
    {α : Type*} [AddGroup α] (g : UnitSphereTwo → α) :
    Function.Odd (fun x : UnitSphereTwo => g x - g (-x)) := by
  intro x
  simpa using (neg_sub (g x) (g (-x))).symm

/-- Helper for Theorem 6.8: continuity of `x ↦ g x - g (-x)` follows from
continuity of `g`. -/
lemma helperForTheorem_6_8_continuous_sub_antipode
    {α : Type*} [TopologicalSpace α] [AddGroup α] [ContinuousAdd α] [ContinuousNeg α]
    (g : UnitSphereTwo → α) (hg : Continuous g) :
    Continuous (fun x : UnitSphereTwo => g x - g (-x)) := by
  simpa [sub_eq_add_neg] using hg.add ((hg.comp continuous_neg).neg)

/-- Helper for Theorem 6.8: every continuous real-valued map on `S²` takes equal
values at some antipodal pair. -/
lemma helperForTheorem_6_8_continuous_real_exists_antipodal_equal
    (g : UnitSphereTwo → ℝ) (hg : Continuous g) :
    ∃ x : UnitSphereTwo, g x = g (-x) := by
  let h : UnitSphereTwo → ℝ := fun x => g x - g (-x)
  have hhcont : Continuous h := by
    simpa [h] using helperForTheorem_6_8_continuous_sub_antipode g hg
  have hhneg : ∀ x : UnitSphereTwo, h (-x) = -h x := by
    simpa [h] using (helperForTheorem_6_8_odd_sub_antipode g)
  have hzero_le_one : (0 : ℝ) ≤ 1 := by
    norm_num
  have hsphereNonempty :
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty := by
    exact (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin 3))) (r := (1 : ℝ))).2
      hzero_le_one
  rcases hsphereNonempty with ⟨x0, hx0⟩
  let xPlus : UnitSphereTwo := ⟨x0, hx0⟩
  letI : ConnectedSpace UnitSphereTwo :=
    helperForTheorem_6_8_connected_space_unitSphereTwo
  have hpre : IsPreconnected (Set.univ : Set UnitSphereTwo) := isPreconnected_univ
  by_cases hle : h xPlus ≤ 0
  · have hneg_nonneg : 0 ≤ h (-xPlus) := by
      rw [hhneg]
      exact neg_nonneg.mpr hle
    have hzero : ∃ x ∈ (Set.univ : Set UnitSphereTwo), h x = 0 := by
      exact
        hpre.intermediate_value₂ (a := xPlus) (b := -xPlus)
          (by simp) (by simp) hhcont.continuousOn continuousOn_const hle hneg_nonneg
    rcases hzero with ⟨x, -, hx⟩
    refine ⟨x, ?_⟩
    dsimp [h] at hx
    linarith
  · have hge : 0 ≤ h xPlus := le_of_lt (lt_of_not_ge hle)
    have hneg_nonpos : h (-xPlus) ≤ 0 := by
      rw [hhneg]
      exact neg_nonpos.mpr hge
    have hzero : ∃ x ∈ (Set.univ : Set UnitSphereTwo), h x = 0 := by
      exact
        hpre.intermediate_value₂ (a := -xPlus) (b := xPlus)
          (by simp) (by simp) hhcont.continuousOn continuousOn_const hneg_nonpos hge
    rcases hzero with ⟨x, -, hx⟩
    refine ⟨x, ?_⟩
    dsimp [h] at hx
    linarith

/-- Helper for Theorem 6.8: an odd continuous real-valued map on `S²` has a zero. -/
lemma helperForTheorem_6_8_continuous_odd_real_exists_zero
    (h : UnitSphereTwo → ℝ) (hcont : Continuous h)
    (hodd : ∀ x : UnitSphereTwo, h (-x) = -h x) :
    ∃ x : UnitSphereTwo, h x = 0 := by
  rcases helperForTheorem_6_8_continuous_real_exists_antipodal_equal h hcont with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  linarith [hx, hodd x]


end Section06
end Chap06
