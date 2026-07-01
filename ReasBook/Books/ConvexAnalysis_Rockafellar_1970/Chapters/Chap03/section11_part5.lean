/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Suwan Wu, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section01_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section11_part4

open scoped Pointwise

section Chap03
section Section11

/-- The closed unit ball `{x | ‖x‖ ≤ 1}` in `Fin n → ℝ` agrees with `Metric.closedBall 0 1`. -/
lemma unitBall_eq_closedBall (n : Nat) :
    ({x : Fin n → Real | ‖x‖ ≤ (1 : Real)} : Set (Fin n → Real)) =
      Metric.closedBall (0 : Fin n → Real) 1 := by
  ext x
  simp

/-- Scalar multiples of the unit ball are the corresponding centered closed balls (for `r ≥ 0`). -/
lemma smul_unitBall_eq_closedBall (n : Nat) {r : Real} (hr : 0 ≤ r) :
    r • ({x : Fin n → Real | ‖x‖ ≤ (1 : Real)} : Set (Fin n → Real)) =
      Metric.closedBall (0 : Fin n → Real) r := by
  calc
    r • ({x : Fin n → Real | ‖x‖ ≤ (1 : Real)} : Set (Fin n → Real)) =
        r • Metric.closedBall (0 : Fin n → Real) 1 := by
          simp [unitBall_eq_closedBall (n := n)]
    _ = Metric.closedBall (0 : Fin n → Real) r := by
          simpa using (smul_unitClosedBall_of_nonneg (E := (Fin n → Real)) (r := r) hr)

/-- Given `b ≠ 0`, there is a unit-ball vector whose dot product with `b` is positive. -/
lemma exists_mem_unitBall_and_dotProduct_pos {n : Nat} {b : Fin n → Real} :
    b ≠ 0 →
      ∃ v : Fin n → Real,
        v ∈ ({x : Fin n → Real | ‖x‖ ≤ (1 : Real)} : Set (Fin n → Real)) ∧ 0 < v ⬝ᵥ b := by
  intro hb0
  rcases Function.ne_iff.mp hb0 with ⟨j, hj⟩
  let a : Real := if 0 ≤ b j then 1 else -1
  let v : Fin n → Real := Pi.single j a
  have hvB : v ∈ ({x : Fin n → Real | ‖x‖ ≤ (1 : Real)} : Set (Fin n → Real)) := by
    have ha : ‖a‖ ≤ (1 : Real) := by
      by_cases h : 0 ≤ b j <;> simp [a, h]
    have hvnorm : ‖v‖ = ‖a‖ := by
      simpa [v] using
        (Pi.norm_single (ι := Fin n) (G := fun _ : Fin n => Real) (i := j) (y := a))
    simpa [hvnorm, v] using ha
  have hvdot : v ⬝ᵥ b = |b j| := by
    have : v ⬝ᵥ b = a * b j := by simp [v]
    by_cases h : 0 ≤ b j
    · have ha : a = 1 := by simp [a, h]
      simp [this, ha, abs_of_nonneg h]
    · have hneg : b j < 0 := lt_of_not_ge h
      have ha : a = -1 := by simp [a, h]
      simp [this, ha, abs_of_neg hneg]
  refine ⟨v, hvB, ?_⟩
  simpa [hvdot] using (mul_pos (show (0 : Real) < 1 by norm_num) (abs_pos.2 hj))

/-- If a `δ`-thickening of `S` is contained in a *closed* half-space `{x | x ⬝ᵥ b ≤ β}`, then
`S` is contained in the corresponding *open* half-space `{x | x ⬝ᵥ b < β}` (for `δ > 0`). -/
lemma strictify_halfspace_le_of_thickening {n : Nat} {S : Set (Fin n → Real)}
    {b : Fin n → Real} {β δ : Real} (hb0 : b ≠ 0) (hδ : 0 < δ)
    (hS : S + (δ • ({x : Fin n → Real | ‖x‖ ≤ (1 : Real)} : Set (Fin n → Real))) ⊆
      {x : Fin n → Real | x ⬝ᵥ b ≤ β}) :
    S ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} := by
  classical
  intro x hx
  rcases exists_mem_unitBall_and_dotProduct_pos (n := n) (b := b) hb0 with ⟨v, hvB, hvpos⟩
  let w : Fin n → Real := δ • v
  have hw : w ∈ δ • ({x : Fin n → Real | ‖x‖ ≤ (1 : Real)} : Set (Fin n → Real)) := by
    exact ⟨v, hvB, rfl⟩
  have hwpos : 0 < w ⬝ᵥ b := by
    simpa [w, smul_dotProduct] using (mul_pos hδ hvpos)
  by_contra hxlt
  have hxge : β ≤ x ⬝ᵥ b := le_of_not_gt hxlt
  have hmem : x + w ∈ S + (δ • ({x : Fin n → Real | ‖x‖ ≤ (1 : Real)} : Set (Fin n → Real))) :=
    ⟨x, hx, w, hw, rfl⟩
  have hle : (x + w) ⬝ᵥ b ≤ β := hS hmem
  have : β < (x + w) ⬝ᵥ b := by
    have : β < x ⬝ᵥ b + w ⬝ᵥ b := by linarith
    simpa [dotProduct_add] using this
  exact (lt_irrefl β) (lt_of_lt_of_le this hle)

/-- If a `δ`-thickening of `S` is contained in a *closed* half-space `{x | β ≤ x ⬝ᵥ b}`, then
`S` is contained in the corresponding *open* half-space `{x | β < x ⬝ᵥ b}` (for `δ > 0`). -/
lemma strictify_halfspace_ge_of_thickening {n : Nat} {S : Set (Fin n → Real)}
    {b : Fin n → Real} {β δ : Real} (hb0 : b ≠ 0) (hδ : 0 < δ)
    (hS : S + (δ • ({x : Fin n → Real | ‖x‖ ≤ (1 : Real)} : Set (Fin n → Real))) ⊆
      {x : Fin n → Real | β ≤ x ⬝ᵥ b}) :
    S ⊆ {x : Fin n → Real | β < x ⬝ᵥ b} := by
  classical
  intro x hx
  rcases exists_mem_unitBall_and_dotProduct_pos (n := n) (b := b) hb0 with ⟨v, hvB, hvpos⟩
  let w : Fin n → Real := δ • v
  have hw : w ∈ δ • ({x : Fin n → Real | ‖x‖ ≤ (1 : Real)} : Set (Fin n → Real)) := by
    exact ⟨v, hvB, rfl⟩
  have hnegw :
      (-w) ∈ δ • ({x : Fin n → Real | ‖x‖ ≤ (1 : Real)} : Set (Fin n → Real)) := by
    refine ⟨-v, ?_, by simp [w]⟩
    simpa [norm_neg] using hvB
  have hwpos : 0 < w ⬝ᵥ b := by
    simpa [w, smul_dotProduct] using (mul_pos hδ hvpos)
  by_contra hxgt
  have hxle : x ⬝ᵥ b ≤ β := le_of_not_gt hxgt
  have hmem :
      x + (-w) ∈ S + (δ • ({x : Fin n → Real | ‖x‖ ≤ (1 : Real)} : Set (Fin n → Real))) :=
    ⟨x, hx, -w, hnegw, rfl⟩
  have hge : β ≤ (x + (-w)) ⬝ᵥ b := hS hmem
  have : (x + (-w)) ⬝ᵥ b < β := by
    have : x ⬝ᵥ b - w ⬝ᵥ b < β := by linarith
    simpa [dotProduct_add, dotProduct_neg, sub_eq_add_neg] using this
  exact (lt_irrefl β) (lt_of_le_of_lt hge this)

/-- If `‖x₁ - x₂‖ ≤ 2ε`, then the midpoint lies in both `ε`-thickenings of `{x₁}` and `{x₂}`. -/
lemma midpoint_mem_add_smul_unitBall_of_norm_sub_le {n : Nat} {x₁ x₂ : Fin n → Real} {ε : Real}
    (hε : 0 ≤ ε) (h : ‖x₁ - x₂‖ ≤ 2 * ε) :
    ∃ z : Fin n → Real,
      z ∈ ({x₁} + (ε • ({x : Fin n → Real | ‖x‖ ≤ (1 : Real)} : Set (Fin n → Real)))) ∧
        z ∈ ({x₂} + (ε • ({x : Fin n → Real | ‖x‖ ≤ (1 : Real)} : Set (Fin n → Real)))) := by
  classical
  let B : Set (Fin n → Real) := {x : Fin n → Real | ‖x‖ ≤ (1 : Real)}
  let z : Fin n → Real := midpoint Real x₁ x₂
  refine ⟨z, ?_, ?_⟩
  · refine ⟨x₁, by simp, z - x₁, ?_, add_sub_cancel x₁ z⟩
    have hdist : dist z x₁ ≤ ε := by
      have hdist12 : dist x₁ x₂ ≤ 2 * ε := by simpa [dist_eq_norm] using h
      calc
        dist z x₁ = (1 / 2 : Real) * dist x₁ x₂ := by
          simp [z]
        _ ≤ (1 / 2 : Real) * (2 * ε) :=
          mul_le_mul_of_nonneg_left hdist12 (by positivity)
        _ = ε := by ring
    have hzmem : z - x₁ ∈ Metric.closedBall (0 : Fin n → Real) ε := by
      have : ‖z - x₁‖ ≤ ε := by
        simpa [dist_eq_norm] using hdist
      exact (mem_closedBall_zero_iff (a := z - x₁) (r := ε)).2 this
    simpa [B, smul_unitBall_eq_closedBall (n := n) (r := ε) hε] using hzmem
  · refine ⟨x₂, by simp, z - x₂, ?_, add_sub_cancel x₂ z⟩
    have hdist : dist z x₂ ≤ ε := by
      have hdist12 : dist x₁ x₂ ≤ 2 * ε := by simpa [dist_eq_norm] using h
      calc
        dist z x₂ = (1 / 2 : Real) * dist x₁ x₂ := by
          simp [z]
        _ ≤ (1 / 2 : Real) * (2 * ε) :=
          mul_le_mul_of_nonneg_left hdist12 (by positivity)
        _ = ε := by ring
    have hzmem : z - x₂ ∈ Metric.closedBall (0 : Fin n → Real) ε := by
      have : ‖z - x₂‖ ≤ ε := by
        simpa [dist_eq_norm] using hdist
      exact (mem_closedBall_zero_iff (a := z - x₂) (r := ε)).2 this
    simpa [B, smul_unitBall_eq_closedBall (n := n) (r := ε) hε] using hzmem

/-- Disjointness of `ε`-thickenings is equivalent to positivity of the infimum of pairwise
distances. -/
lemma exists_eps_disjoint_thickenings_iff_sInf_norm_sub_pos (n : Nat)
    (C₁ C₂ : Set (Fin n → Real)) (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty) :
    (∃ ε : Real, 0 < ε ∧
        let B : Set (Fin n → Real) := {x : Fin n → Real | ‖x‖ ≤ (1 : Real)}
        Disjoint (C₁ + (ε • B)) (C₂ + (ε • B))) ↔
      0 < sInf (Set.image2 (fun x₁ x₂ : Fin n → Real => ‖x₁ - x₂‖) C₁ C₂) := by
  classical
  let B : Set (Fin n → Real) := {x : Fin n → Real | ‖x‖ ≤ (1 : Real)}
  let D : Set Real := Set.image2 (fun x₁ x₂ : Fin n → Real => ‖x₁ - x₂‖) C₁ C₂
  have hDne : D.Nonempty := by
    rcases hC₁ne with ⟨x₁, hx₁⟩
    rcases hC₂ne with ⟨x₂, hx₂⟩
    exact ⟨‖x₁ - x₂‖, x₁, hx₁, x₂, hx₂, rfl⟩
  have hDbdd : BddBelow D := by
    refine ⟨0, ?_⟩
    intro d hd
    rcases hd with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    exact norm_nonneg (x₁ - x₂)
  constructor
  · rintro ⟨ε, hεpos, hdisj⟩
    have hεnonneg : 0 ≤ ε := le_of_lt hεpos
    have hLower : ∀ d ∈ D, 2 * ε ≤ d := by
      intro d hd
      rcases hd with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
      have hlt : 2 * ε < ‖x₁ - x₂‖ := by
        by_contra hle
        have hle' : ‖x₁ - x₂‖ ≤ 2 * ε := le_of_not_gt hle
        -- Midpoint lies in both thickenings, contradicting disjointness.
        rcases midpoint_mem_add_smul_unitBall_of_norm_sub_le (n := n) (x₁ := x₁) (x₂ := x₂)
            (ε := ε) hεnonneg hle' with ⟨z, hz₁, hz₂⟩
        have hz₁' : z ∈ C₁ + (ε • B) := by
          rcases hz₁ with ⟨x, hx, u, hu, rfl⟩
          have hx' : x = x₁ := by
            simpa [Set.mem_singleton_iff] using hx
          subst x
          exact ⟨x₁, hx₁, u, hu, rfl⟩
        have hz₂' : z ∈ C₂ + (ε • B) := by
          rcases hz₂ with ⟨x, hx, u, hu, rfl⟩
          have hx' : x = x₂ := by
            simpa [Set.mem_singleton_iff] using hx
          subst x
          exact ⟨x₂, hx₂, u, hu, rfl⟩
        exact (Set.disjoint_left.1 hdisj hz₁' hz₂')
      exact le_of_lt hlt
    have hle : 2 * ε ≤ sInf D := le_csInf hDne hLower
    have hpos : 0 < 2 * ε := by nlinarith
    have : 0 < sInf D := lt_of_lt_of_le hpos hle
    simpa [D] using this
  · intro hpos
    have hDpos : 0 < sInf D := by simpa [D] using hpos
    -- Take `ε = (sInf D) / 4`.
    refine ⟨(sInf D) / 4, by nlinarith [hDpos], ?_⟩
    · -- Show disjointness by contradiction: an intersection gives a too-small distance.
      have hεpos : 0 < (sInf D) / 4 := by
        have : 0 < sInf D := hDpos
        nlinarith
      have hεnonneg : 0 ≤ (sInf D) / 4 := le_of_lt hεpos
      refine Set.disjoint_left.2 ?_
      intro z hz₁ hz₂
      rcases hz₁ with ⟨x₁, hx₁, u, hu, rfl⟩
      rcases hz₂ with ⟨x₂, hx₂, v, hv, hvEq⟩
      -- `x₁ - x₂` has norm at most `‖v‖ + ‖u‖ ≤ 2ε`.
      have hu' : ‖u‖ ≤ (sInf D) / 4 := by
        have hu0 : u ∈ Metric.closedBall (0 : Fin n → Real) ((sInf D) / 4) := by
          simpa [B, smul_unitBall_eq_closedBall (n := n) (r := (sInf D) / 4) hεnonneg] using hu
        simpa using (mem_closedBall_zero_iff.1 hu0)
      have hv' : ‖v‖ ≤ (sInf D) / 4 := by
        have hv0 : v ∈ Metric.closedBall (0 : Fin n → Real) ((sInf D) / 4) := by
          simpa [B, smul_unitBall_eq_closedBall (n := n) (r := (sInf D) / 4) hεnonneg] using hv
        simpa using (mem_closedBall_zero_iff.1 hv0)
      have hdist_le : ‖x₁ - x₂‖ ≤ 2 * ((sInf D) / 4) := by
        have hEq : x₁ + u = x₂ + v := by
          simpa [add_assoc, add_comm, add_left_comm] using hvEq.symm
        have : x₁ - x₂ = v - u := by
          have h' := congrArg (fun t : Fin n → Real => t - x₂ - u) hEq
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
        -- use triangle inequality on `v - u`.
        calc
          ‖x₁ - x₂‖ = ‖v - u‖ := by simp [this]
          _ ≤ ‖v‖ + ‖u‖ := norm_sub_le _ _
          _ ≤ (sInf D) / 4 + (sInf D) / 4 := add_le_add hv' hu'
          _ = 2 * ((sInf D) / 4) := by ring
      have hmem : ‖x₁ - x₂‖ ∈ D := ⟨x₁, hx₁, x₂, hx₂, rfl⟩
      have hcsInf : sInf D ≤ ‖x₁ - x₂‖ := csInf_le hDbdd hmem
      have : sInf D ≤ (sInf D) / 2 := by
        have : sInf D ≤ 2 * ((sInf D) / 4) := le_trans hcsInf hdist_le
        nlinarith
      exact (not_le_of_gt hDpos) (by nlinarith)

/-- Strong separation is equivalent to disjointness of some `ε`-thickenings. -/
lemma exists_hyperplaneSeparatesStrongly_iff_exists_eps_disjoint_thickenings (n : Nat)
    (C₁ C₂ : Set (Fin n → Real)) (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex Real C₁) (hC₂conv : Convex Real C₂) :
    (∃ H, HyperplaneSeparatesStrongly n H C₁ C₂) ↔
      ∃ ε : Real, 0 < ε ∧
        let B : Set (Fin n → Real) := {x : Fin n → Real | ‖x‖ ≤ (1 : Real)}
        Disjoint (C₁ + (ε • B)) (C₂ + (ε • B)) := by
  classical
  let B : Set (Fin n → Real) := {x : Fin n → Real | ‖x‖ ≤ (1 : Real)}
  constructor
  · rintro ⟨H, hH⟩
    rcases hH with ⟨_, _, b, β, hb0, hHdef, ε, hεpos, hcases⟩
    refine ⟨ε, hεpos, ?_⟩
    have hcases' :
        ((C₁ + (ε • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∧
              C₂ + (ε • B) ⊆ {x : Fin n → Real | β < x ⬝ᵥ b}) ∨
          (C₂ + (ε • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∧
              C₁ + (ε • B) ⊆ {x : Fin n → Real | β < x ⬝ᵥ b})) := by
      simpa [B] using hcases
    have hhalf :
        Disjoint {x : Fin n → Real | x ⬝ᵥ b < β} {x : Fin n → Real | β < x ⬝ᵥ b} := by
      refine Set.disjoint_left.2 ?_
      intro x hx1 hx2
      exact (lt_irrefl β) (lt_trans hx2 hx1)
    cases hcases' with
    | inl h =>
        exact (hhalf.mono h.1 h.2)
    | inr h =>
        -- swap the disjoint half-spaces
        simpa [disjoint_comm] using (hhalf.mono h.1 h.2)
  · rintro ⟨ε, hεpos, hdisj⟩
    have hεnonneg : 0 ≤ ε := le_of_lt hεpos
    -- Proper separation of the `ε`-thickenings.
    let A₁ : Set (Fin n → Real) := C₁ + (ε • B)
    let A₂ : Set (Fin n → Real) := C₂ + (ε • B)
    have hA₁ne : A₁.Nonempty := by
      rcases hC₁ne with ⟨x, hx⟩
      have h0B : (0 : Fin n → Real) ∈ ε • B := by
        refine ⟨0, by simp [B], by simp⟩
      exact ⟨x, ⟨x, hx, 0, h0B, by simp⟩⟩
    have hA₂ne : A₂.Nonempty := by
      rcases hC₂ne with ⟨x, hx⟩
      have h0B : (0 : Fin n → Real) ∈ ε • B := by
        refine ⟨0, by simp [B], by simp⟩
      exact ⟨x, ⟨x, hx, 0, h0B, by simp⟩⟩
    have hBconv : Convex Real B := by
      -- `B` is a centered closed ball.
      simpa [B, unitBall_eq_closedBall (n := n)] using
        (convex_closedBall (0 : Fin n → Real) (1 : Real))
    have hεBconv : Convex Real (ε • B) := hBconv.smul ε
    have hA₁conv : Convex Real A₁ := hC₁conv.add hεBconv
    have hA₂conv : Convex Real A₂ := hC₂conv.add hεBconv
    have hriDisj : Disjoint (intrinsicInterior Real A₁) (intrinsicInterior Real A₂) := by
      exact hdisj.mono intrinsicInterior_subset intrinsicInterior_subset
    have hProper :
        ∃ H, HyperplaneSeparatesProperly n H A₁ A₂ := by
      exact
        (exists_hyperplaneSeparatesProperly_iff_disjoint_intrinsicInterior n A₁ A₂ hA₁ne hA₂ne
              hA₁conv hA₂conv).2
          hriDisj
    rcases hProper with ⟨H, hHproper⟩
    rcases hyperplaneSeparatesProperly_oriented n H A₁ A₂ hHproper with
      ⟨b, β, hb0, hH, hA₁β, hA₂β, hnot⟩
    -- Shrink the thickening radius to `ε/2` and strictify.
    let ε' : Real := ε / 2
    have hε'pos : 0 < ε' := by
      dsimp [ε']
      nlinarith [hεpos]
    have hε'nonneg : 0 ≤ ε' := le_of_lt hε'pos
    have hA₁thick : (C₁ + (ε' • B)) + (ε' • B) ⊆ A₁ := by
      intro z hz
      rcases hz with ⟨y, hy, t, ht, rfl⟩
      rcases hy with ⟨x, hx, u, hu, rfl⟩
      refine ⟨x, hx, u + t, ?_, by simp [add_assoc]⟩
      -- `u + t ∈ ε•B` because `u,t ∈ ε'•B` and `ε = ε' + ε'`.
      have hu' : u ∈ Metric.closedBall (0 : Fin n → Real) ε' := by
        simpa [B, smul_unitBall_eq_closedBall (n := n) (r := ε') hε'nonneg] using hu
      have ht' : t ∈ Metric.closedBall (0 : Fin n → Real) ε' := by
        simpa [B, smul_unitBall_eq_closedBall (n := n) (r := ε') hε'nonneg] using ht
      have hsum : u + t ∈ Metric.closedBall (0 : Fin n → Real) ε := by
        have : Metric.closedBall (0 : Fin n → Real) ε' + Metric.closedBall (0 : Fin n → Real) ε' =
            Metric.closedBall (0 : Fin n → Real) (ε' + ε') := by
          simpa using
            (closedBall_add_closedBall (E := (Fin n → Real)) (hε := hε'nonneg) (hδ := hε'nonneg)
              (a := (0 : Fin n → Real)) (b := (0 : Fin n → Real)))
        have hmem : u + t ∈
            Metric.closedBall (0 : Fin n → Real) ε' + Metric.closedBall (0 : Fin n → Real) ε' :=
          ⟨u, hu', t, ht', rfl⟩
        have : u + t ∈ Metric.closedBall (0 : Fin n → Real) (ε' + ε') := by
          simpa [this] using hmem
        have hrad : ε' + ε' = ε := by
          dsimp [ε']
          ring
        simpa [hrad] using this
      simpa [B, smul_unitBall_eq_closedBall (n := n) (r := ε) hεnonneg] using hsum
    have hA₂thick : (C₂ + (ε' • B)) + (ε' • B) ⊆ A₂ := by
      intro z hz
      rcases hz with ⟨y, hy, t, ht, rfl⟩
      rcases hy with ⟨x, hx, u, hu, rfl⟩
      refine ⟨x, hx, u + t, ?_, by simp [add_assoc]⟩
      have hu' : u ∈ Metric.closedBall (0 : Fin n → Real) ε' := by
        simpa [B, smul_unitBall_eq_closedBall (n := n) (r := ε') hε'nonneg] using hu
      have ht' : t ∈ Metric.closedBall (0 : Fin n → Real) ε' := by
        simpa [B, smul_unitBall_eq_closedBall (n := n) (r := ε') hε'nonneg] using ht
      have hsum : u + t ∈ Metric.closedBall (0 : Fin n → Real) ε := by
        have : Metric.closedBall (0 : Fin n → Real) ε' + Metric.closedBall (0 : Fin n → Real) ε' =
            Metric.closedBall (0 : Fin n → Real) (ε' + ε') := by
          simpa using
            (closedBall_add_closedBall (E := (Fin n → Real)) (hε := hε'nonneg) (hδ := hε'nonneg)
              (a := (0 : Fin n → Real)) (b := (0 : Fin n → Real)))
        have hmem : u + t ∈
            Metric.closedBall (0 : Fin n → Real) ε' + Metric.closedBall (0 : Fin n → Real) ε' :=
          ⟨u, hu', t, ht', rfl⟩
        have : u + t ∈ Metric.closedBall (0 : Fin n → Real) (ε' + ε') := by
          simpa [this] using hmem
        have hrad : ε' + ε' = ε := by
          dsimp [ε']
          ring
        simpa [hrad] using this
      simpa [B, smul_unitBall_eq_closedBall (n := n) (r := ε) hεnonneg] using hsum
    have hC₁open : C₁ + (ε' • B) ⊆ {x : Fin n → Real | β < x ⬝ᵥ b} := by
      refine strictify_halfspace_ge_of_thickening (n := n) (S := C₁ + (ε' • B)) (b := b)
        (β := β) (δ := ε') hb0 hε'pos ?_
      intro x hx
      have hx' : x ∈ A₁ := hA₁thick hx
      exact hA₁β x hx'
    have hC₂open : C₂ + (ε' • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} := by
      refine strictify_halfspace_le_of_thickening (n := n) (S := C₂ + (ε' • B)) (b := b)
        (β := β) (δ := ε') hb0 hε'pos ?_
      intro x hx
      have hx' : x ∈ A₂ := hA₂thick hx
      exact hA₂β x hx'
    refine ⟨H, ?_⟩
    refine ⟨hC₁ne, hC₂ne, b, β, hb0, hH, ε', hε'pos, ?_⟩
    -- match the orientation in the definition (`C₂` on the left, `C₁` on the right).
    dsimp [B]
    exact Or.inr ⟨hC₂open, hC₁open⟩

/-- The distance-set between `C₁` and `C₂` is the image of `dist 0` on `C₁ - C₂`. -/
lemma image2_norm_sub_eq_image_dist_sub (n : Nat) (C₁ C₂ : Set (Fin n → Real)) :
    Set.image2 (fun x₁ x₂ : Fin n → Real => ‖x₁ - x₂‖) C₁ C₂ =
      (fun z : Fin n → Real => dist (0 : Fin n → Real) z) '' (C₁ - C₂) := by
  ext r
  constructor
  · rintro ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    refine ⟨x₁ - x₂, ?_, ?_⟩
    · exact ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    · simpa using (dist_zero_left (x₁ - x₂))
  · rintro ⟨z, hz, rfl⟩
    rcases hz with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    refine ⟨x₁, hx₁, x₂, hx₂, ?_⟩
    simpa using (dist_zero_left (x₁ - x₂)).symm

/-- Positivity of the infimum distance-set is equivalent to `0 ∉ closure (C₁ - C₂)`. -/
lemma sInf_norm_sub_pos_iff_zero_not_mem_closure_sub (n : Nat)
    (C₁ C₂ : Set (Fin n → Real)) (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty) :
    0 < sInf (Set.image2 (fun x₁ x₂ : Fin n → Real => ‖x₁ - x₂‖) C₁ C₂) ↔
      (0 : Fin n → Real) ∉ closure (C₁ - C₂) := by
  classical
  have hsub_ne : (C₁ - C₂).Nonempty := by
    rcases hC₁ne with ⟨x₁, hx₁⟩
    rcases hC₂ne with ⟨x₂, hx₂⟩
    exact ⟨x₁ - x₂, x₁, hx₁, x₂, hx₂, rfl⟩
  -- Rewrite the `sInf` as an `infDist`.
  have hEq :
      sInf (Set.image2 (fun x₁ x₂ : Fin n → Real => ‖x₁ - x₂‖) C₁ C₂) =
        Metric.infDist (0 : Fin n → Real) (C₁ - C₂) := by
    have hglb :
        IsGLB ((fun z : Fin n → Real => dist (0 : Fin n → Real) z) '' (C₁ - C₂))
          (Metric.infDist (0 : Fin n → Real) (C₁ - C₂)) :=
      Metric.isGLB_infDist hsub_ne
    -- Use the greatest lower bound characterization of `sInf`.
    have :
        sInf ((fun z : Fin n → Real => dist (0 : Fin n → Real) z) '' (C₁ - C₂)) =
          Metric.infDist (0 : Fin n → Real) (C₁ - C₂) :=
      by
        have himage_ne :
            ((fun z : Fin n → Real => dist (0 : Fin n → Real) z) '' (C₁ - C₂)).Nonempty :=
          hsub_ne.image (fun z : Fin n → Real => dist (0 : Fin n → Real) z)
        exact hglb.csInf_eq himage_ne
    simpa [image2_norm_sub_eq_image_dist_sub (n := n) (C₁ := C₁) (C₂ := C₂)] using this
  -- Now apply the standard metric characterization of `closure`.
  -- `x ∉ closure s ↔ 0 < infDist x s`.
  simpa [hEq] using
    (Metric.infDist_pos_iff_notMem_closure (x := (0 : Fin n → Real)) (s := (C₁ - C₂)) hsub_ne).symm

/-- Theorem 11.4: Let `C₁` and `C₂` be non-empty convex sets in `ℝ^n`. In order that there exist a
hyperplane separating `C₁` and `C₂` strongly, it is necessary and sufficient that

`inf { ‖x₁ - x₂‖ | x₁ ∈ C₁, x₂ ∈ C₂ } > 0`,

in other words that `0 ∉ closure (C₁ - C₂)`. -/
theorem exists_hyperplaneSeparatesStrongly_iff_inf_sub_norm_pos (n : Nat)
    (C₁ C₂ : Set (Fin n → Real)) (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex Real C₁) (hC₂conv : Convex Real C₂) :
    (∃ H, HyperplaneSeparatesStrongly n H C₁ C₂) ↔
      0 < sInf (Set.image2 (fun x₁ x₂ : Fin n → Real => ‖x₁ - x₂‖) C₁ C₂) := by
  -- Strong separation ↔ disjoint thickenings ↔ positive distance infimum.
  have h₁ :
      (∃ H, HyperplaneSeparatesStrongly n H C₁ C₂) ↔
        ∃ ε : Real, 0 < ε ∧
          let B : Set (Fin n → Real) := {x : Fin n → Real | ‖x‖ ≤ (1 : Real)}
          Disjoint (C₁ + (ε • B)) (C₂ + (ε • B)) :=
    exists_hyperplaneSeparatesStrongly_iff_exists_eps_disjoint_thickenings n C₁ C₂ hC₁ne hC₂ne
      hC₁conv hC₂conv
  have h₂ :
      (∃ ε : Real, 0 < ε ∧
          let B : Set (Fin n → Real) := {x : Fin n → Real | ‖x‖ ≤ (1 : Real)}
          Disjoint (C₁ + (ε • B)) (C₂ + (ε • B))) ↔
        0 < sInf (Set.image2 (fun x₁ x₂ : Fin n → Real => ‖x₁ - x₂‖) C₁ C₂) :=
    exists_eps_disjoint_thickenings_iff_sInf_norm_sub_pos n C₁ C₂ hC₁ne hC₂ne
  exact h₁.trans h₂

/-- Theorem 11.4 (closure form): Let `C₁` and `C₂` be non-empty convex sets in `ℝ^n`. There exists a
hyperplane separating `C₁` and `C₂` strongly if and only if `0 ∉ closure (C₁ - C₂)`. -/
theorem exists_hyperplaneSeparatesStrongly_iff_zero_not_mem_closure_sub (n : Nat)
    (C₁ C₂ : Set (Fin n → Real)) (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex Real C₁) (hC₂conv : Convex Real C₂) :
    (∃ H, HyperplaneSeparatesStrongly n H C₁ C₂) ↔
      (0 : Fin n → Real) ∉ closure (C₁ - C₂) := by
  -- Combine the infimum-distance form with the standard metric characterization of `closure`.
  have h :=
    exists_hyperplaneSeparatesStrongly_iff_inf_sub_norm_pos (n := n) (C₁ := C₁) (C₂ := C₂) hC₁ne
      hC₂ne hC₁conv hC₂conv
  have h' :=
    sInf_norm_sub_pos_iff_zero_not_mem_closure_sub (n := n) (C₁ := C₁) (C₂ := C₂) hC₁ne hC₂ne
  exact h.trans h'

/-- Disjointness implies `0 ∉ (C₁ - C₂)`. -/
lemma zero_not_mem_sub_of_disjoint {E : Type*} [AddGroup E] {C₁ C₂ : Set E}
    (hdisj : Disjoint C₁ C₂) :
    (0 : E) ∉ (C₁ - C₂) := by
  intro h0
  rcases (Set.mem_sub.1 h0) with ⟨x₁, hx₁, x₂, hx₂, hsub⟩
  have hEq : x₁ = x₂ := sub_eq_zero.mp (by simpa using hsub)
  subst hEq
  exact (Set.disjoint_left.1 hdisj hx₁ hx₂)

/-- Recession directions of a negated set are the negations of recession directions. -/
lemma recessionCone_neg_set_iff {E : Type*} [AddCommGroup E] [Module Real E] (C : Set E) (y : E) :
    y ∈ Set.recessionCone (-C) ↔ (-y) ∈ Set.recessionCone C := by
  constructor
  · intro hy x hx t ht
    have hx' : (-x) ∈ (-C) := by simpa using hx
    have hmem : (-x) + t • y ∈ (-C) := hy hx' ht
    -- `-( (-x) + t•y ) = x + t•(-y)`.
    have : -((-x) + t • y) ∈ C := by simpa using hmem
    simpa [neg_add, add_assoc, add_left_comm, add_comm, smul_neg] using this
  · intro hy x hx t ht
    have hx' : (-x) ∈ C := by simpa using hx
    have hmem : (-x) + t • (-y) ∈ C := hy hx' ht
    -- Membership in `-C` is preimage under negation.
    have hmem' : (-x) + (-(t • y)) ∈ C := by
      simpa [smul_neg] using hmem
    have : -(x + t • y) ∈ C := by
      -- Rewrite the goal into the form provided by `hmem'`.
      rw [neg_add]
      exact hmem'
    simpa using this

/-- Membership in a recession cone is preserved under preimages by linear equivalences. -/
lemma mem_recessionCone_preimage_linearEquiv_iff
    {E F : Type*} [AddCommGroup E] [Module Real E] [AddCommGroup F] [Module Real F]
    (φ : E ≃ₗ[Real] F) (C : Set F) (y : E) :
    y ∈ Set.recessionCone (φ ⁻¹' C) ↔ φ y ∈ Set.recessionCone C := by
  constructor
  · intro hy x hx t ht
    have hxE : φ.symm x ∈ φ ⁻¹' C := by simpa using hx
    have hmem : φ.symm x + t • y ∈ φ ⁻¹' C := hy hxE ht
    have : φ (φ.symm x + t • y) ∈ C := hmem
    simpa [φ.map_add, φ.map_smul] using this
  · intro hy x hx t ht
    have hx' : φ x ∈ C := hx
    have : φ x + t • φ y ∈ C := hy hx' ht
    have : φ (x + t • y) ∈ C := by simpa [φ.map_add, φ.map_smul] using this
    exact this

/-- Under the recession-condition hypothesis, the Minkowski difference `C₁ - C₂` is closed. -/
lemma isClosed_sub_of_noCommonRecessionDirections (n : Nat) (C₁ C₂ : Set (Fin n → Real))
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty) (hC₁closed : IsClosed C₁) (hC₂closed : IsClosed C₂)
    (hC₁conv : Convex Real C₁) (hC₂conv : Convex Real C₂)
    (hrec : ∀ y, y ≠ (0 : Fin n → Real) → y ∈ Set.recessionCone C₁ → y ∈ Set.recessionCone C₂ →
      False) :
    IsClosed (C₁ - C₂) := by
  classical
  /- Transport the closedness statement to `EuclideanSpace` (the `ℓ^2` norm) via the canonical
     continuous linear equivalence `PiLp 2 ≃L Π`. -/
  let e :
      EuclideanSpace Real (Fin n) ≃L[Real] (Fin n → Real) := by
    simpa [EuclideanSpace] using
      (PiLp.continuousLinearEquiv (p := (2 : ENNReal)) (𝕜 := Real) (β := fun _ : Fin n => Real))
  let A : Set (EuclideanSpace Real (Fin n)) := e ⁻¹' C₁
  let B : Set (EuclideanSpace Real (Fin n)) := e ⁻¹' C₂

  have hAne : A.Nonempty := by
    rcases hC₁ne with ⟨x, hx⟩
    refine ⟨e.symm x, ?_⟩
    simpa [A] using hx
  have hBne : B.Nonempty := by
    rcases hC₂ne with ⟨x, hx⟩
    refine ⟨e.symm x, ?_⟩
    simpa [B] using hx
  have hAclosed : IsClosed A := by
    simpa [A] using hC₁closed.preimage e.continuous
  have hBclosed : IsClosed B := by
    simpa [B] using hC₂closed.preimage e.continuous
  have hAconv : Convex Real A := by
    simpa [A] using hC₁conv.linear_preimage e.toLinearEquiv.toLinearMap
  have hBconv : Convex Real B := by
    simpa [B] using hC₂conv.linear_preimage e.toLinearEquiv.toLinearMap
  have hBne' : (-B).Nonempty := by
    rcases hBne with ⟨x, hx⟩
    refine ⟨-x, ?_⟩
    simpa using hx
  have hBclosed' : IsClosed (-B) := by
    simpa using hBclosed.preimage (continuous_neg : Continuous fun x : EuclideanSpace Real (Fin n) => -x)
  have hBconv' : Convex Real (-B) := hBconv.neg

  have hrec' : ∀ y, y ∈ Set.recessionCone C₁ → y ∈ Set.recessionCone C₂ → y = (0 : Fin n → Real) := by
    intro y hy₁ hy₂
    by_cases hy0 : y = 0
    · simp [hy0]
    · exfalso
      exact hrec y hy0 hy₁ hy₂

  have hopp :
      ∀ z,
        z ∈ Set.recessionCone A → -z ∈ Set.recessionCone (-B) → z = 0 := by
    intro z hzA hzneg
    have hzB : z ∈ Set.recessionCone B := by
      have : -(-z) ∈ Set.recessionCone B :=
        (recessionCone_neg_set_iff (C := B) (y := -z)).1 hzneg
      simpa using this
    -- Transport to the original sets and use `hrec'`.
    have hzC₁' : e.toLinearEquiv z ∈ Set.recessionCone C₁ :=
      (mem_recessionCone_preimage_linearEquiv_iff e.toLinearEquiv C₁ z).1 hzA
    have hzC₂' : e.toLinearEquiv z ∈ Set.recessionCone C₂ :=
      (mem_recessionCone_preimage_linearEquiv_iff e.toLinearEquiv C₂ z).1 hzB
    have hzC₁ : e z ∈ Set.recessionCone C₁ := by simpa using hzC₁'
    have hzC₂ : e z ∈ Set.recessionCone C₂ := by simpa using hzC₂'
    have : e z = 0 := hrec' (e z) hzC₁ hzC₂
    exact e.injective this

  have hclosed_add :
      IsClosed (A + (-B)) :=
    (closed_add_recessionCone_eq_of_no_opposite_recession (C1 := A) (C2 := -B) (hC1ne := hAne)
          (hC2ne := hBne') (hC1conv := hAconv) (hC2conv := hBconv') (hC1closed := hAclosed)
          (hC2closed := hBclosed') (hopp := hopp)).1
  have hClosedAB : IsClosed (A - B) := by
    simpa [set_sub_eq_add_neg A B] using hclosed_add
  -- Transport back to the product model `Fin n → ℝ`.
  have hClosedImage : IsClosed (e '' (A - B)) :=
    (Homeomorph.isClosed_image (h := e.toHomeomorph) (s := A - B)).2 hClosedAB
  have himage : e '' (A - B) = C₁ - C₂ := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases (Set.mem_sub.1 hz) with ⟨a, ha, b, hb, rfl⟩
      refine Set.mem_sub.2 ?_
      refine ⟨e a, ha, e b, hb, by simp⟩
    · intro hx
      rcases (Set.mem_sub.1 hx) with ⟨a, ha, b, hb, rfl⟩
      refine ⟨(e.symm a) - (e.symm b), ?_, by simp⟩
      refine Set.mem_sub.2 ?_
      refine ⟨e.symm a, ?_, e.symm b, ?_, rfl⟩
      · simpa [A] using ha
      · simpa [B] using hb
  simpa [himage] using hClosedImage

/-- Corollary 11.4.1. Let `C₁` and `C₂` be non-empty disjoint closed convex sets in `ℝ^n`
having no common directions of recession. Then there exists a hyperplane separating `C₁` and
`C₂` strongly. -/
theorem exists_hyperplaneSeparatesStrongly_of_disjoint_closed_convex_noCommonRecessionDirections
    (n : Nat) (C₁ C₂ : Set (Fin n → Real)) (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁closed : IsClosed C₁) (hC₂closed : IsClosed C₂) (hC₁conv : Convex Real C₁)
    (hC₂conv : Convex Real C₂) (hdisj : Disjoint C₁ C₂)
    (hrec : ∀ y, y ≠ (0 : Fin n → Real) → y ∈ Set.recessionCone C₁ → y ∈ Set.recessionCone C₂ →
      False) :
    ∃ H, HyperplaneSeparatesStrongly n H C₁ C₂ := by
  have h0not : (0 : Fin n → Real) ∉ closure (C₁ - C₂) := by
    have h0not' : (0 : Fin n → Real) ∉ (C₁ - C₂) := zero_not_mem_sub_of_disjoint (hdisj := hdisj)
    have hClosed : IsClosed (C₁ - C₂) :=
      isClosed_sub_of_noCommonRecessionDirections n C₁ C₂ hC₁ne hC₂ne hC₁closed hC₂closed hC₁conv
        hC₂conv hrec
    simpa [hClosed.closure_eq] using h0not'
  exact
    (exists_hyperplaneSeparatesStrongly_iff_zero_not_mem_closure_sub (n := n) (C₁ := C₁) (C₂ := C₂)
          hC₁ne hC₂ne hC₁conv hC₂conv).2
      h0not

/-- Bounded sets in `Fin n → ℝ` have only the zero recession direction. -/
lemma recessionCone_subset_singleton_of_bounded_fin {n : Nat} {C : Set (Fin n → Real)}
    (hCne : C.Nonempty) (hCbdd : Bornology.IsBounded C) :
    Set.recessionCone C ⊆ {0} := by
  intro y hy
  by_contra hy0
  rcases hCne with ⟨x0, hx0⟩
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  rcases hCbdd.subset_closedBall (0 : Fin n → Real) with ⟨R, hR⟩
  have hx0R : ‖x0‖ ≤ R := by
    have hx0mem : x0 ∈ Metric.closedBall (0 : Fin n → Real) R := hR hx0
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx0mem
  have hRnonneg : 0 ≤ R := le_trans (norm_nonneg _) hx0R
  set t : ℝ := (R + ‖x0‖ + 1) / ‖y‖
  have ht_nonneg : 0 ≤ t := by
    have hnum : 0 ≤ R + ‖x0‖ + 1 := by
      linarith [hRnonneg, norm_nonneg x0]
    exact div_nonneg hnum (le_of_lt hypos)
  have hx_t : x0 + t • y ∈ C := hy hx0 ht_nonneg
  have hx_t_R : ‖x0 + t • y‖ ≤ R := by
    have hx_t_mem : x0 + t • y ∈ Metric.closedBall (0 : Fin n → Real) R := hR hx_t
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx_t_mem
  have htriangle : ‖t • y‖ ≤ ‖x0 + t • y‖ + ‖x0‖ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (norm_sub_le (x0 + t • y) x0)
  have hnorm_bound : ‖t • y‖ ≤ R + ‖x0‖ := by
    linarith [htriangle, hx_t_R]
  have hnorm_t : ‖t • y‖ = t * ‖y‖ := by
    calc
      ‖t • y‖ = ‖t‖ * ‖y‖ := norm_smul _ _
      _ = t * ‖y‖ := by
            simp [Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
  have hbound : t * ‖y‖ ≤ R + ‖x0‖ := by
    simpa [hnorm_t] using hnorm_bound
  have ht_eq : t * ‖y‖ = R + ‖x0‖ + 1 := by
    have hyne : ‖y‖ ≠ 0 := ne_of_gt hypos
    calc
      t * ‖y‖ = ((R + ‖x0‖ + 1) / ‖y‖) * ‖y‖ := by simp [t]
      _ = R + ‖x0‖ + 1 := by
            field_simp [hyne]
  have : (R + ‖x0‖ + 1 : ℝ) ≤ R + ‖x0‖ := by
    simpa [ht_eq] using hbound
  linarith

/-- If one of two sets is bounded, then their closures have no common nonzero recession direction. -/
lemma noCommonRecessionDirections_closure_of_bounded_side {n : Nat} {C₁ C₂ : Set (Fin n → Real)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hbounded : Bornology.IsBounded C₁ ∨ Bornology.IsBounded C₂) :
    ∀ y, y ≠ (0 : Fin n → Real) → y ∈ Set.recessionCone (closure C₁) →
      y ∈ Set.recessionCone (closure C₂) → False := by
  classical
  cases hbounded with
  | inl hC₁bdd =>
      have hC₁bdd' : Bornology.IsBounded (closure C₁) := hC₁bdd.closure
      have hrec0 : Set.recessionCone (closure C₁) ⊆ {0} :=
        recessionCone_subset_singleton_of_bounded_fin (C := closure C₁) hC₁ne.closure hC₁bdd'
      intro y hy0 hy₁ _hy₂
      have : y = (0 : Fin n → Real) := by
        have hy' : y ∈ ({0} : Set (Fin n → Real)) := hrec0 hy₁
        simpa [Set.mem_singleton_iff] using hy'
      exact hy0 this
  | inr hC₂bdd =>
      have hC₂bdd' : Bornology.IsBounded (closure C₂) := hC₂bdd.closure
      have hrec0 : Set.recessionCone (closure C₂) ⊆ {0} :=
        recessionCone_subset_singleton_of_bounded_fin (C := closure C₂) hC₂ne.closure hC₂bdd'
      intro y hy0 _hy₁ hy₂
      have : y = (0 : Fin n → Real) := by
        have hy' : y ∈ ({0} : Set (Fin n → Real)) := hrec0 hy₂
        simpa [Set.mem_singleton_iff] using hy'
      exact hy0 this

/-- Strong hyperplane separation is monotone under shrinking the separated sets. -/
lemma hyperplaneSeparatesStrongly_mono_sets {n : Nat} {H A₁ A₂ B₁ B₂ : Set (Fin n → Real)}
    (hH : HyperplaneSeparatesStrongly n H A₁ A₂) (hB₁ : B₁ ⊆ A₁) (hB₂ : B₂ ⊆ A₂)
    (hB₁ne : B₁.Nonempty) (hB₂ne : B₂.Nonempty) :
    HyperplaneSeparatesStrongly n H B₁ B₂ := by
  classical
  rcases hH with ⟨_hA₁ne, _hA₂ne, b, β, hb0, hHdef, ε, hεpos, hcases⟩
  refine ⟨hB₁ne, hB₂ne, b, β, hb0, hHdef, ε, hεpos, ?_⟩
  let B : Set (Fin n → Real) := {x : Fin n → Real | ‖x‖ ≤ (1 : Real)}
  have hcases' :
      ((A₁ + (ε • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∧
            A₂ + (ε • B) ⊆ {x : Fin n → Real | β < x ⬝ᵥ b}) ∨
        (A₂ + (ε • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∧
          A₁ + (ε • B) ⊆ {x : Fin n → Real | β < x ⬝ᵥ b})) := by
    simpa [B] using hcases
  have hthick₁ : B₁ + (ε • B) ⊆ A₁ + (ε • B) := by
    intro x hx
    rcases hx with ⟨x₁, hx₁, u, hu, rfl⟩
    exact ⟨x₁, hB₁ hx₁, u, hu, rfl⟩
  have hthick₂ : B₂ + (ε • B) ⊆ A₂ + (ε • B) := by
    intro x hx
    rcases hx with ⟨x₂, hx₂, u, hu, rfl⟩
    exact ⟨x₂, hB₂ hx₂, u, hu, rfl⟩
  have hcasesB :
      ((B₁ + (ε • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∧
            B₂ + (ε • B) ⊆ {x : Fin n → Real | β < x ⬝ᵥ b}) ∨
        (B₂ + (ε • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∧
          B₁ + (ε • B) ⊆ {x : Fin n → Real | β < x ⬝ᵥ b})) := by
    cases hcases' with
    | inl h =>
        refine Or.inl ?_
        refine ⟨?_, ?_⟩
        · intro x hx
          exact h.1 (hthick₁ hx)
        · intro x hx
          exact h.2 (hthick₂ hx)
    | inr h =>
        refine Or.inr ?_
        refine ⟨?_, ?_⟩
        · intro x hx
          exact h.1 (hthick₂ hx)
        · intro x hx
          exact h.2 (hthick₁ hx)
  simpa [B] using hcasesB

/-- Corollary 11.4.2. Let `C₁` and `C₂` be non-empty convex sets in `ℝ^n` whose closures are
disjoint. If either set is bounded, there exists a hyperplane separating `C₁` and `C₂`
strongly. -/
theorem exists_hyperplaneSeparatesStrongly_of_disjoint_closure_convex_of_bounded (n : Nat)
    (C₁ C₂ : Set (Fin n → Real)) (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex Real C₁) (hC₂conv : Convex Real C₂)
    (hdisj : Disjoint (closure C₁) (closure C₂))
    (hbounded : Bornology.IsBounded C₁ ∨ Bornology.IsBounded C₂) :
    ∃ H, HyperplaneSeparatesStrongly n H C₁ C₂ := by
  have hrec :
      ∀ y, y ≠ (0 : Fin n → Real) → y ∈ Set.recessionCone (closure C₁) →
        y ∈ Set.recessionCone (closure C₂) → False :=
    noCommonRecessionDirections_closure_of_bounded_side (C₁ := C₁) (C₂ := C₂) hC₁ne hC₂ne hbounded
  rcases
      exists_hyperplaneSeparatesStrongly_of_disjoint_closed_convex_noCommonRecessionDirections
        (n := n) (C₁ := closure C₁) (C₂ := closure C₂) hC₁ne.closure hC₂ne.closure isClosed_closure
        isClosed_closure hC₁conv.closure hC₂conv.closure hdisj hrec with
    ⟨H, hH⟩
  refine ⟨H, ?_⟩
  exact
    hyperplaneSeparatesStrongly_mono_sets (n := n) (H := H) (A₁ := closure C₁) (A₂ := closure C₂)
      (B₁ := C₁) (B₂ := C₂) hH subset_closure subset_closure hC₁ne hC₂ne

/-- A single dot-product inequality defines a closed half-space. -/
lemma isClosed_setOf_dotProduct_le {n : Nat} (b : Fin n → Real) (β : Real) :
    IsClosed {x : Fin n → Real | x ⬝ᵥ b ≤ β} := by
  have hcont : Continuous fun x : Fin n → Real => x ⬝ᵥ b := by
    simpa using (continuous_id.dotProduct (continuous_const : Continuous fun _ : Fin n → Real => b))
  simpa [Set.preimage, Set.mem_Iic] using (isClosed_Iic.preimage hcont)

/-- A single dot-product inequality defines a convex half-space. -/
lemma convex_setOf_dotProduct_le {n : Nat} (b : Fin n → Real) (β : Real) :
    Convex Real {x : Fin n → Real | x ⬝ᵥ b ≤ β} := by
  simpa using
    (convex_halfSpace_le (𝕜 := Real) (f := fun x : Fin n → Real => x ⬝ᵥ b)
      (isLinearMap_dotProduct_left (n := n) b) β)

/-- A system of dot-product inequalities is the intersection of the corresponding half-spaces. -/
lemma setOf_forall_dotProduct_le_eq_iInter (n : Nat) (I : Type*) (b : I → Fin n → Real)
    (β : I → Real) :
    {x : Fin n → Real | ∀ i : I, x ⬝ᵥ b i ≤ β i} =
      ⋂ i : I, {x : Fin n → Real | x ⬝ᵥ b i ≤ β i} := by
  ext x
  simp

/-- Text 11.2.1: The solution set `S` of a system of weak linear inequalities
`⟪x, b i⟫ ≤ β i` (i.e. `x ⬝ᵥ b i ≤ β i`, for all `i ∈ I`) is a closed convex set. -/
theorem isClosed_and_convex_setOf_dotProduct_le (n : Nat) (I : Type*) (b : I → Fin n → Real)
    (β : I → Real) :
    IsClosed {x : Fin n → Real | ∀ i : I, x ⬝ᵥ b i ≤ β i} ∧
      Convex Real {x : Fin n → Real | ∀ i : I, x ⬝ᵥ b i ≤ β i} := by
  constructor
  · -- Closedness: intersection of closed half-spaces.
    simpa [setOf_forall_dotProduct_le_eq_iInter (n := n) (I := I) (b := b) (β := β)] using
      (isClosed_iInter fun i : I => isClosed_setOf_dotProduct_le (n := n) (b := b i) (β := β i))
  · -- Convexity: intersection of convex half-spaces.
    simpa [setOf_forall_dotProduct_le_eq_iInter (n := n) (I := I) (b := b) (β := β)] using
      (convex_iInter fun i : I => convex_setOf_dotProduct_le (n := n) (b := b i) (β := β i))

/-- Text 11.3.1: Let `C` be a convex set in `ℝ^n`. A supporting half-space to `C` is a closed
half-space which contains `C` and has a point of `C` in its boundary. -/
def IsClosedHalfspace (n : Nat) (H : Set (Fin n → Real)) : Prop :=
  ∃ (b : Fin n → Real) (β : Real),
    b ≠ 0 ∧ (H = {x : Fin n → Real | x ⬝ᵥ b ≤ β} ∨ H = {x : Fin n → Real | β ≤ x ⬝ᵥ b})

/-- Text 11.3.1: Let `C` be a convex set in `ℝ^n`. A supporting half-space to `C` is a closed
half-space which contains `C` and has a point of `C` in its boundary. -/
def IsSupportingHalfspace (n : Nat) (C H : Set (Fin n → Real)) : Prop :=
  Convex Real C ∧ IsClosedHalfspace n H ∧ C ⊆ H ∧ ∃ x, x ∈ C ∧ x ∈ frontier H

/-- Text 11.3.2: A supporting hyperplane to `C` is a hyperplane which is the boundary of a
supporting half-space to `C`. Equivalently, a supporting hyperplane has the form
`H = {x | x ⬝ᵥ b = β}` with `b ≠ 0`, such that `x ⬝ᵥ b ≤ β` for every `x ∈ C` and
`x ⬝ᵥ b = β` for at least one `x ∈ C`. -/
def IsSupportingHyperplane (n : Nat) (C H : Set (Fin n → Real)) : Prop :=
  ∃ (b : Fin n → Real) (β : Real),
    b ≠ 0 ∧
      H = {x : Fin n → Real | x ⬝ᵥ b = β} ∧
        (∀ x, x ∈ C → x ⬝ᵥ b ≤ β) ∧ ∃ x, x ∈ C ∧ x ⬝ᵥ b = β

/-- If a nonempty affine subspace is not `⊤`, then its direction is a proper submodule. -/
lemma direction_ne_top_of_ne_top_of_nonempty {n : Nat} {A : AffineSubspace ℝ (Fin n → Real)}
    (hAne : (A : Set (Fin n → Real)).Nonempty) (hA : A ≠ ⊤) :
    A.direction ≠ ⊤ := by
  intro hdir
  have : A = ⊤ :=
    (AffineSubspace.direction_eq_top_iff_of_nonempty (k := ℝ) (V := Fin n → Real)
      (P := Fin n → Real) (s := A) hAne).1 hdir
  exact hA this

/-- If a linear functional vanishes on the direction of an affine subspace, then it is constant
on that affine subspace. -/
lemma affineSubspace_subset_setOf_apply_eq_of_le_ker_direction
    {V : Type*} [AddCommGroup V] [Module ℝ V] (A : AffineSubspace ℝ V) {x0 : V} (hx0 : x0 ∈ A)
    (f : Module.Dual ℝ V) (hdir : A.direction ≤ LinearMap.ker f) :
    (A : Set V) ⊆ {x : V | f x = f x0} := by
  intro x hx
  have hv : x -ᵥ x0 ∈ A.direction := A.vsub_mem_direction hx hx0
  have hker : x -ᵥ x0 ∈ LinearMap.ker f := hdir hv
  have hsub : f (x -ᵥ x0) = 0 := by
    simpa [LinearMap.mem_ker] using hker
  have : f x - f x0 = 0 := by
    simpa [vsub_eq_sub, map_sub] using hsub
  exact sub_eq_zero.mp this

/-- In `Fin n → ℝ` with `0 < n`, one can choose an explicit nonzero vector. -/
lemma empty_case_choose_nonzero_b {n : Nat} (hn : 0 < n) :
    ∃ b : Fin n → Real, b ≠ 0 := by
  classical
  let j : Fin n := ⟨0, hn⟩
  refine ⟨Pi.single j (1 : Real), ?_⟩
  exact Function.ne_iff.2 ⟨j, by simp [j]⟩

/-- Text 11.3.3: If `C` is not `n`-dimensional (so that `affineSpan ℝ C ≠ ⊤`), then there exists
a hyperplane containing (and hence extending) `affineSpan ℝ C`, and therefore containing all of
`C`. -/
theorem exists_hyperplane_superset_affineSpan_of_affineSpan_ne_top (n : Nat) (hn : 0 < n)
    (C : Set (Fin n → Real))
    (hC : affineSpan ℝ C ≠ (⊤ : AffineSubspace ℝ (Fin n → Real))) :
    ∃ (b : Fin n → Real) (β : Real),
      b ≠ 0 ∧
        C ⊆ {x : Fin n → Real | x ⬝ᵥ b = β} ∧
          (affineSpan ℝ C : Set (Fin n → Real)) ⊆ {x : Fin n → Real | x ⬝ᵥ b = β} := by
  classical
  by_cases hCne : C.Nonempty
  · rcases hCne with ⟨x0, hx0C⟩
    have hx0A : x0 ∈ affineSpan ℝ C := subset_affineSpan ℝ C hx0C
    have hAne : (affineSpan ℝ C : Set (Fin n → Real)).Nonempty := ⟨x0, hx0A⟩
    have hdir_ne_top :
        (affineSpan ℝ C).direction ≠ (⊤ : Submodule ℝ (Fin n → Real)) :=
      direction_ne_top_of_ne_top_of_nonempty (n := n) (A := affineSpan ℝ C) hAne hC
    have hdir_lt_top : (affineSpan ℝ C).direction < (⊤ : Submodule ℝ (Fin n → Real)) :=
      lt_top_iff_ne_top.2 hdir_ne_top
    rcases
        Submodule.exists_le_ker_of_lt_top (p := (affineSpan ℝ C).direction) hdir_lt_top with
      ⟨f, hf0, hdir_le_ker⟩
    rcases dual_eq_dotProductLinear n f hf0 with ⟨b, hb0, hfb⟩
    subst hfb
    refine ⟨b, x0 ⬝ᵥ b, hb0, ?_, ?_⟩
    · have hAset :
          (affineSpan ℝ C : Set (Fin n → Real)) ⊆
            {x : Fin n → Real | x ⬝ᵥ b = x0 ⬝ᵥ b} := by
        have hAset' :
            (affineSpan ℝ C : Set (Fin n → Real)) ⊆
              {x : Fin n → Real | (dotProductLinear n b) x = (dotProductLinear n b) x0} :=
          affineSubspace_subset_setOf_apply_eq_of_le_ker_direction
            (A := affineSpan ℝ C) hx0A (f := dotProductLinear n b) hdir_le_ker
        simpa [dotProductLinear] using hAset'
      exact Set.Subset.trans (subset_affineSpan ℝ C) (by simpa using hAset)
    · have hAset :
          (affineSpan ℝ C : Set (Fin n → Real)) ⊆
            {x : Fin n → Real | x ⬝ᵥ b = x0 ⬝ᵥ b} := by
        have hAset' :
            (affineSpan ℝ C : Set (Fin n → Real)) ⊆
              {x : Fin n → Real | (dotProductLinear n b) x = (dotProductLinear n b) x0} :=
          affineSubspace_subset_setOf_apply_eq_of_le_ker_direction
            (A := affineSpan ℝ C) hx0A (f := dotProductLinear n b) hdir_le_ker
        simpa [dotProductLinear] using hAset'
      simpa using hAset
  · have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hCne
    subst hCempty
    rcases empty_case_choose_nonzero_b (n := n) hn with ⟨b, hb0⟩
    refine ⟨b, (0 : Real), hb0, ?_, ?_⟩ <;> simp

/-- Text 11.3.4: We usually speak only of non-trivial supporting hyperplanes to `C`, i.e. those
supporting hyperplanes `H` which do not contain `C` itself. -/
def IsNontrivialSupportingHyperplane (n : Nat) (C H : Set (Fin n → Real)) : Prop :=
  IsSupportingHyperplane n C H ∧ ¬ C ⊆ H

/-- The dot product with `b` as a continuous linear functional, viewed in the `StrongDual`. -/
noncomputable def dotProduct_strongDual {n : Nat} (b : Fin n → Real) :
    StrongDual ℝ (Fin n → Real) :=
  LinearMap.toContinuousLinearMap
    (IsLinearMap.mk' (fun x : Fin n → Real => x ⬝ᵥ b) (isLinearMap_dotProduct_left (n := n) b))

@[simp] lemma dotProduct_strongDual_apply {n : Nat} (b x : Fin n → Real) :
    dotProduct_strongDual (n := n) b x = x ⬝ᵥ b := by
  simp [dotProduct_strongDual]

/-- If `a ∉ C` and `C` is a nonempty closed convex set in `ℝ^n`, then there exists a continuous
linear functional that strictly separates `a` from `C`. -/
lemma exists_strongDual_strict_sep_point_of_not_mem_isClosed_convex {n : Nat}
    {a : Fin n → Real} {C : Set (Fin n → Real)} (hCconv : Convex Real C) (hCclosed : IsClosed C)
    (hCne : C.Nonempty) (ha : a ∉ C) :
    ∃ l : StrongDual ℝ (Fin n → Real), ∀ y ∈ C, l y < l a := by
  classical
  have hdisj' : Disjoint ({a} : Set (Fin n → Real)) C :=
    (Set.disjoint_singleton_left.2 ha)
  have hdisj : Disjoint (closure ({a} : Set (Fin n → Real))) (closure C) := by
    simpa [closure_singleton, hCclosed.closure_eq] using hdisj'
  have hbounded : Bornology.IsBounded ({a} : Set (Fin n → Real)) ∨ Bornology.IsBounded C :=
    Or.inl Bornology.isBounded_singleton
  rcases
      exists_hyperplaneSeparatesStrongly_of_disjoint_closure_convex_of_bounded (n := n) ({a} : _)
        C (Set.singleton_nonempty a) hCne (convex_singleton (𝕜 := Real) (c := a)) hCconv hdisj
        hbounded with
    ⟨H, hH⟩
  rcases hH with ⟨_h₁ne, _h₂ne, b, β, hb0, _hHdef, ε, hεpos, hcases⟩
  let B : Set (Fin n → Real) := {x : Fin n → Real | ‖x‖ ≤ (1 : Real)}
  have hcases' :
      (({a} + (ε • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∧
            C + (ε • B) ⊆ {x : Fin n → Real | β < x ⬝ᵥ b}) ∨
        (C + (ε • B) ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∧
          {a} + (ε • B) ⊆ {x : Fin n → Real | β < x ⬝ᵥ b})) := by
    simpa [B] using hcases
  have h0B : (0 : Fin n → Real) ∈ ε • B := by
    refine ⟨0, ?_, by simp⟩
    simp [B]
  have ha_thick : a ∈ ({a} + (ε • B)) := by
    refine ⟨a, by simp, 0, h0B, by simp⟩
  cases hcases' with
  | inl h =>
      have ha_lt : a ⬝ᵥ b < β := h.1 ha_thick
      have hC_gt : ∀ y ∈ C, β < y ⬝ᵥ b := by
        intro y hyC
        have hy_thick : y ∈ C + (ε • B) := by
          refine ⟨y, hyC, 0, h0B, by simp⟩
        exact h.2 hy_thick
      refine ⟨dotProduct_strongDual (n := n) (-b), ?_⟩
      intro y hyC
      have hy_gt_a : a ⬝ᵥ b < y ⬝ᵥ b := lt_trans ha_lt (hC_gt y hyC)
      have : -(y ⬝ᵥ b) < -(a ⬝ᵥ b) := neg_lt_neg hy_gt_a
      simpa [dotProduct_strongDual_apply, dotProduct_neg] using this
  | inr h =>
      have ha_gt : β < a ⬝ᵥ b := h.2 ha_thick
      have hC_lt : ∀ y ∈ C, y ⬝ᵥ b < β := by
        intro y hyC
        have hy_thick : y ∈ C + (ε • B) := by
          refine ⟨y, hyC, 0, h0B, by simp⟩
        exact h.1 hy_thick
      refine ⟨dotProduct_strongDual (n := n) b, ?_⟩
      intro y hyC
      exact lt_trans (hC_lt y hyC) ha_gt

end Section11
end Chap03
