/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section07_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section14_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section12_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section15_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section15_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section15_part7

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise
open scoped Topology
open Filter

/-- The Euclidean norm scales linearly with scalar multiplication. -/
lemma piEuclideanNorm_smul {n : ℕ} (r : ℝ) (x : Fin n → ℝ) :
    Real.sqrt (dotProduct (r • x) (r • x)) = |r| * Real.sqrt (dotProduct x x) := by
  have hr2 : 0 ≤ r * r := by nlinarith
  calc
    Real.sqrt (dotProduct (r • x) (r • x)) = Real.sqrt (r * r * dotProduct x x) := by
      simp [dotProduct_smul, smul_eq_mul, mul_comm, mul_left_comm]
    _ = Real.sqrt (r * r) * Real.sqrt (dotProduct x x) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (Real.sqrt_mul hr2 (dotProduct x x))
    _ = |r| * Real.sqrt (dotProduct x x) := by
      have h : Real.sqrt (r * r) = |r| := by
        simpa [pow_two] using (Real.sqrt_sq_eq_abs r)
      simp [h]

/-- Comparison of the sup norm with the Euclidean norm on `Fin n → ℝ`. -/
lemma supNorm_le_piEuclideanNorm_and_piEuclideanNorm_le_sqrt_n_mul_supNorm {n : ℕ}
    (x : Fin n → ℝ) :
    ‖x‖ ≤ Real.sqrt (dotProduct x x) ∧
      Real.sqrt (dotProduct x x) ≤ Real.sqrt (n : ℝ) * ‖x‖ := by
  constructor
  · have hnonneg : 0 ≤ Real.sqrt (dotProduct x x) := Real.sqrt_nonneg _
    refine (pi_norm_le_iff_of_nonneg (x := x) (r := Real.sqrt (dotProduct x x)) hnonneg).2 ?_
    intro i
    have hnonneg' : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (x j) ^ 2 := by
      intro j hj
      nlinarith
    have hmem : i ∈ (Finset.univ : Finset (Fin n)) := by simp
    have hsum : (x i) ^ 2 ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)), (x j) ^ 2 :=
      Finset.single_le_sum hnonneg' hmem
    have hsq : (x i) ^ 2 ≤ dotProduct x x := by
      simpa [dotProduct, pow_two, mul_comm, mul_left_comm, mul_assoc] using hsum
    have habs : |x i| ≤ Real.sqrt (dotProduct x x) := Real.abs_le_sqrt hsq
    simpa using habs
  · have hcoord : ∀ i, ‖x i‖ ≤ ‖x‖ := by
      have h := (pi_norm_le_iff_of_nonneg (x := x) (r := ‖x‖) (norm_nonneg _)).1 (le_rfl)
      simpa using h
    have hterm : ∀ i, x i * x i ≤ ‖x‖ ^ 2 := by
      intro i
      have habs : |x i| ≤ ‖x‖ := by simpa using hcoord i
      have hsq : |x i| * |x i| ≤ ‖x‖ * ‖x‖ := by
        exact mul_self_le_mul_self (abs_nonneg _) habs
      simpa [pow_two, abs_mul_abs_self] using hsq
    have hsum : dotProduct x x ≤ (n : ℝ) * ‖x‖ ^ 2 := by
      have hsum' : ∑ i : Fin n, x i * x i ≤ ∑ i : Fin n, ‖x‖ ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact hterm i
      have hsum'' : ∑ i : Fin n, ‖x‖ ^ 2 = (n : ℝ) * ‖x‖ ^ 2 := by
        classical
        simp
      have hsum''' : ∑ i : Fin n, x i * x i ≤ (n : ℝ) * ‖x‖ ^ 2 := by
        simpa [hsum''] using hsum'
      simpa [dotProduct] using hsum'''
    have hnonneg : 0 ≤ Real.sqrt (n : ℝ) * ‖x‖ := by
      exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hEq : (Real.sqrt (n : ℝ) * ‖x‖) ^ 2 = (n : ℝ) * ‖x‖ ^ 2 := by
      have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      calc
        (Real.sqrt (n : ℝ) * ‖x‖) ^ 2 = (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) * (‖x‖ * ‖x‖) := by
          ring
        _ = (n : ℝ) * ‖x‖ ^ 2 := by
          simp [pow_two, Real.mul_self_sqrt hn]
    have hsq : dotProduct x x ≤ (Real.sqrt (n : ℝ) * ‖x‖) ^ 2 := by
      simpa [hEq] using hsum
    exact (Real.sqrt_le_iff).2 ⟨hnonneg, hsq⟩

/-- A neighborhood of `0` contains a scaled Euclidean unit ball. -/
lemma exists_pos_smul_piEuclideanUnitBall_subset_of_zero_mem_interior {n : ℕ}
    {C : Set (Fin n → ℝ)} (hC0 : (0 : Fin n → ℝ) ∈ interior C) :
    ∃ α : ℝ, 0 < α ∧ (fun x => α • x) '' piEuclideanUnitBall n ⊆ C := by
  have hnhds : C ∈ 𝓝 (0 : Fin n → ℝ) := mem_interior_iff_mem_nhds.mp hC0
  rcases (Metric.mem_nhds_iff.mp hnhds) with ⟨r, hrpos, hball⟩
  refine ⟨r / 2, by linarith, ?_⟩
  intro x hx
  rcases hx with ⟨y, hyB, rfl⟩
  have hy_norm : ‖y‖ ≤ 1 := by
    have hle := (supNorm_le_piEuclideanNorm_and_piEuclideanNorm_le_sqrt_n_mul_supNorm (n := n) y).1
    have hyB' : Real.sqrt (dotProduct y y) ≤ (1 : ℝ) := by
      simpa [piEuclideanUnitBall] using hyB
    exact le_trans hle hyB'
  have hnorm_le : ‖(r / 2) • y‖ ≤ r / 2 := by
    calc
      ‖(r / 2) • y‖ = ‖(r / 2)‖ * ‖y‖ := by
        simpa using (norm_smul (r / 2) y)
      _ = |r / 2| * ‖y‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ |r / 2| * 1 := by
        exact mul_le_mul_of_nonneg_left hy_norm (abs_nonneg _)
      _ = r / 2 := by
        have hrpos' : 0 < r / 2 := by linarith
        simp [abs_of_pos hrpos']
  have hnorm_lt : ‖(r / 2) • y‖ < r := by
    exact lt_of_le_of_lt hnorm_le (by linarith)
  have hmem : (r / 2) • y ∈ Metric.ball (0 : Fin n → ℝ) r := by
    have : dist ((r / 2) • y) (0 : Fin n → ℝ) < r := by
      simpa [dist_eq_norm] using hnorm_lt
    simpa [Metric.mem_ball] using this
  exact hball hmem

/-- A bounded set is contained in a scaled Euclidean unit ball. -/
lemma exists_pos_smul_piEuclideanUnitBall_superset_of_isBounded {n : ℕ}
    {C : Set (Fin n → ℝ)} (hC_bdd : Bornology.IsBounded C) :
    ∃ β : ℝ, 0 < β ∧ (C ⊆ (fun x => β • x) '' piEuclideanUnitBall n) := by
  rcases hC_bdd.subset_closedBall (0 : Fin n → ℝ) with ⟨R, hCsub⟩
  set β : ℝ := Real.sqrt (n : ℝ) * max R 1 + 1
  have hβpos : 0 < β := by
    have hmax : 0 ≤ max R 1 := by
      have : (0 : ℝ) ≤ 1 := by linarith
      exact le_trans this (le_max_right _ _)
    have hnonneg : 0 ≤ Real.sqrt (n : ℝ) * max R 1 :=
      mul_nonneg (Real.sqrt_nonneg _) hmax
    dsimp [β]
    linarith
  refine ⟨β, hβpos, ?_⟩
  intro x hx
  have hxball : x ∈ Metric.closedBall (0 : Fin n → ℝ) R := hCsub hx
  have hxnorm : ‖x‖ ≤ R := by
    have : dist x (0 : Fin n → ℝ) ≤ R := by
      simpa [Metric.mem_closedBall] using hxball
    simpa [dist_eq_norm] using this
  have hEuclid : Real.sqrt (dotProduct x x) ≤ Real.sqrt (n : ℝ) * ‖x‖ :=
    (supNorm_le_piEuclideanNorm_and_piEuclideanNorm_le_sqrt_n_mul_supNorm (n := n) x).2
  have hnorm_le : ‖x‖ ≤ max R 1 := le_trans hxnorm (le_max_left _ _)
  have hmul_le : Real.sqrt (n : ℝ) * ‖x‖ ≤ Real.sqrt (n : ℝ) * max R 1 := by
    exact mul_le_mul_of_nonneg_left hnorm_le (Real.sqrt_nonneg _)
  have hbound : Real.sqrt (dotProduct x x) ≤ Real.sqrt (n : ℝ) * max R 1 :=
    le_trans hEuclid hmul_le
  have hbound' : Real.sqrt (dotProduct x x) ≤ β := by
    dsimp [β]
    linarith [hbound]
  have hβne : β ≠ 0 := ne_of_gt hβpos
  have hmem : (1 / β) • x ∈ piEuclideanUnitBall n := by
    have hscale : Real.sqrt (dotProduct ((1 / β) • x) ((1 / β) • x)) =
        |1 / β| * Real.sqrt (dotProduct x x) :=
      piEuclideanNorm_smul (n := n) (r := 1 / β) x
    have hpos : 0 < (1 / β) := one_div_pos.mpr hβpos
    have habs : |1 / β| = (1 / β) := abs_of_pos hpos
    have hmul : (1 / β) * Real.sqrt (dotProduct x x) ≤ (1 / β) * β := by
      exact mul_le_mul_of_nonneg_left hbound' (le_of_lt hpos)
    have hmul' : (1 / β) * β = 1 := one_div_mul_cancel hβne
    have hle : (1 / β) * Real.sqrt (dotProduct x x) ≤ (1 : ℝ) := by
      calc
        (1 / β) * Real.sqrt (dotProduct x x) ≤ (1 / β) * β := hmul
        _ = 1 := hmul'
    have hscale' :
        Real.sqrt (dotProduct ((1 / β) • x) ((1 / β) • x)) =
          (1 / β) * Real.sqrt (dotProduct x x) := by
      calc
        Real.sqrt (dotProduct ((1 / β) • x) ((1 / β) • x)) =
            |1 / β| * Real.sqrt (dotProduct x x) := hscale
        _ = (1 / β) * Real.sqrt (dotProduct x x) := by
          rw [habs]
    have hle' : Real.sqrt (dotProduct ((1 / β) • x) ((1 / β) • x)) ≤ (1 : ℝ) := by
      calc
        Real.sqrt (dotProduct ((1 / β) • x) ((1 / β) • x)) =
            (1 / β) * Real.sqrt (dotProduct x x) := hscale'
        _ ≤ 1 := hle
    simpa [piEuclideanUnitBall] using hle'
  refine ⟨(1 / β) • x, hmem, ?_⟩
  simp [β, smul_smul, one_div, hβne]

/-- Bounds on `ρ` from the unit-ball sandwich and the ball formula. -/
lemma rho_bounds_of_ball_eq_and_unitBall_sandwich {n : ℕ}
    {C : Set (Fin n → ℝ)} {ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {α β : ℝ}
    (hαpos : 0 < α) (hβpos : 0 < β)
    (hCα : (fun x => α • x) '' piEuclideanUnitBall n ⊆ C)
    (hCβ : C ⊆ (fun x => β • x) '' piEuclideanUnitBall n)
    (hρdiag : ∀ x, ρ x x = 0)
    (hρpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (hball : ∀ x ε, 0 < ε → {y | ρ x y ≤ ε} = (fun c => x + ε • c) '' C) :
    ∀ x y : Fin n → ℝ,
      β⁻¹ * piEuclideanDist x y ≤ ρ x y ∧ ρ x y ≤ α⁻¹ * piEuclideanDist x y := by
  intro x y
  by_cases hxy : x = y
  · subst hxy
    simp [piEuclideanDist, hρdiag]
  · have hρpos' : 0 < ρ x y := hρpos x y hxy
    have hdist_pos : 0 < piEuclideanDist x y := by
      have hnonneg : 0 ≤ dotProduct (x - y) (x - y) :=
        dotProduct_self_nonneg (v := x - y)
      have hne : dotProduct (x - y) (x - y) ≠ 0 := by
        intro hzero
        have hxy' : x - y = 0 := (dotProduct_self_eq_zero (v := x - y)).1 hzero
        exact hxy (sub_eq_zero.mp hxy')
      have hpos : 0 < dotProduct (x - y) (x - y) :=
        lt_of_le_of_ne hnonneg (Ne.symm hne)
      exact (Real.sqrt_pos.mpr hpos)
    -- upper bound
    have hupper : ρ x y ≤ α⁻¹ * piEuclideanDist x y := by
      rcases exists_unitBall_smul_eq (n := n) (x := x - y) with ⟨b, hbB, hbEq⟩
      have hbEq' : x - y = piEuclideanDist x y • b := by
        simpa [piEuclideanDist] using hbEq
      have hbBneg : -b ∈ piEuclideanUnitBall n := by
        have hbB' : Real.sqrt (dotProduct b b) ≤ (1 : ℝ) := by
          simpa [piEuclideanUnitBall] using hbB
        have : Real.sqrt (dotProduct (-b) (-b)) ≤ (1 : ℝ) := by
          simpa [dotProduct] using hbB'
        simpa [piEuclideanUnitBall] using this
      have hcC : (-α) • b ∈ C := by
        have : α • (-b) ∈ C := hCα ⟨-b, hbBneg, rfl⟩
        simpa [smul_neg, neg_smul] using this
      set ε : ℝ := α⁻¹ * piEuclideanDist x y
      have hεpos : 0 < ε := by
        have hαinv : 0 < α⁻¹ := inv_pos.mpr hαpos
        have : 0 < α⁻¹ * piEuclideanDist x y := mul_pos hαinv hdist_pos
        simpa [ε] using this
      have hy : y = x + ε • ((-α) • b) := by
        have hscale : ε • ((-α) • b) = -(piEuclideanDist x y) • b := by
          have hαne : α ≠ 0 := ne_of_gt hαpos
          calc
            ε • ((-α) • b) = (ε * -α) • b := by simp [smul_smul]
            _ = (-(piEuclideanDist x y)) • b := by
              simp [ε, hαne, mul_comm]
        calc
          y = x - (x - y) := by abel
          _ = x + (-(piEuclideanDist x y) • b) := by
            simp [hbEq', sub_eq_add_neg]
          _ = x + ε • ((-α) • b) := by
            rw [hscale]
      have hyball : y ∈ {y | ρ x y ≤ ε} := by
        have : y ∈ (fun c => x + ε • c) '' C := ⟨(-α) • b, hcC, hy.symm⟩
        simpa [hball x ε hεpos] using this
      simpa [ε] using hyball
    -- lower bound
    have hlower : β⁻¹ * piEuclideanDist x y ≤ ρ x y := by
      have hyball : y ∈ {z | ρ x z ≤ ρ x y} := by simp
      have hball' : y ∈ (fun c => x + (ρ x y) • c) '' C := by
        have hball_symm :
            (fun c => x + (ρ x y) • c) '' C = {z | ρ x z ≤ ρ x y} :=
          (hball x (ρ x y) hρpos').symm
        rw [hball_symm]
        exact hyball
      rcases hball' with ⟨c, hcC, hcy⟩
      rcases hCβ hcC with ⟨b, hbB, hcb⟩
      have hbB' : Real.sqrt (dotProduct b b) ≤ (1 : ℝ) := by
        simpa [piEuclideanUnitBall] using hbB
      have hcy' : y - x = (ρ x y) • c := by
        calc
          y - x = x + (ρ x y) • c - x := by simp [hcy]
          _ = (ρ x y) • c := by abel
      have hxy' : x - y = -(ρ x y) • c := by
        calc
          x - y = -(y - x) := by abel
          _ = -(ρ x y) • c := by simp [hcy']
      have hcb' : c = β • b := hcb.symm
      have hdist_le : piEuclideanDist x y ≤ (ρ x y) * β := by
        have hscale : x - y = (-(ρ x y) * β) • b := by
          simp [hxy', hcb', smul_smul, mul_comm]
        have hdist_eq : piEuclideanDist x y = |-(ρ x y) * β| * Real.sqrt (dotProduct b b) := by
          have := piEuclideanNorm_smul (n := n) (r := (-(ρ x y) * β)) b
          simpa [piEuclideanDist, hscale] using this
        have hpos : 0 < (ρ x y) * β := by nlinarith [hρpos', hβpos]
        have habs : |-(ρ x y) * β| = (ρ x y) * β := by
          simp [abs_neg, abs_of_pos hpos]
        calc
          piEuclideanDist x y = |-(ρ x y) * β| * Real.sqrt (dotProduct b b) := hdist_eq
          _ ≤ |-(ρ x y) * β| * 1 := by
            exact mul_le_mul_of_nonneg_left hbB' (abs_nonneg _)
          _ = (ρ x y) * β := by
            rw [habs]
            simp
      have hβnonneg : 0 ≤ β⁻¹ := by
        exact inv_nonneg.mpr (le_of_lt hβpos)
      have hmul : β⁻¹ * piEuclideanDist x y ≤ β⁻¹ * ((ρ x y) * β) :=
        mul_le_mul_of_nonneg_left hdist_le hβnonneg
      have hmul' : β⁻¹ * ((ρ x y) * β) = ρ x y := by
        field_simp [hβpos.ne']
      simpa [hmul'] using hmul
    exact ⟨hlower, hupper⟩

/-- Two-sided bounds between distance functions give equivalent open/closed/Cauchy notions. -/
lemma isOpen_isClosed_cauchy_equiv_of_two_sided_bounds {α : Type*}
    {d₁ d₂ : α → α → ℝ} {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hbound : ∀ x y, c₁ * d₁ x y ≤ d₂ x y ∧ d₂ x y ≤ c₂ * d₁ x y) :
    (∀ s : Set α, IsOpenOfDistFun d₂ s ↔ IsOpenOfDistFun d₁ s) ∧
      (∀ s : Set α, IsClosedOfDistFun d₂ s ↔ IsClosedOfDistFun d₁ s) ∧
        (∀ u : ℕ → α, CauchySeqOfDistFun d₂ u ↔ CauchySeqOfDistFun d₁ u) := by
  have hopen : ∀ s : Set α, IsOpenOfDistFun d₂ s ↔ IsOpenOfDistFun d₁ s := by
    intro s
    constructor
    · intro hs x hx
      rcases hs x hx with ⟨ε, hεpos, hε⟩
      have hεpos' : 0 < ε / c₂ := div_pos hεpos hc₂
      refine ⟨ε / c₂, hεpos', ?_⟩
      intro y hy
      have hle : d₂ x y ≤ c₂ * d₁ x y := (hbound x y).2
      have hy' : d₂ x y < ε := by
        have h := mul_lt_mul_of_pos_left hy hc₂
        have hc₂ne : c₂ ≠ 0 := ne_of_gt hc₂
        have h' : c₂ * (ε / c₂) = ε := by field_simp [hc₂ne]
        exact lt_of_le_of_lt hle (by simpa [h'] using h)
      exact hε y hy'
    · intro hs x hx
      rcases hs x hx with ⟨ε, hεpos, hε⟩
      have hεpos' : 0 < c₁ * ε := mul_pos hc₁ hεpos
      refine ⟨c₁ * ε, hεpos', ?_⟩
      intro y hy
      have hle : c₁ * d₁ x y ≤ d₂ x y := (hbound x y).1
      have hy' : d₁ x y < ε := by
        have : c₁ * d₁ x y < c₁ * ε := lt_of_le_of_lt hle hy
        exact (lt_of_mul_lt_mul_left this (le_of_lt hc₁))
      exact hε y hy'
  have hclosed : ∀ s : Set α, IsClosedOfDistFun d₂ s ↔ IsClosedOfDistFun d₁ s := by
    intro s
    simpa [IsClosedOfDistFun] using (hopen sᶜ)
  have hcauchy : ∀ u : ℕ → α, CauchySeqOfDistFun d₂ u ↔ CauchySeqOfDistFun d₁ u := by
    intro u
    constructor
    · intro hu ε hεpos
      have hεpos' : 0 < c₁ * ε := mul_pos hc₁ hεpos
      rcases hu (c₁ * ε) hεpos' with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro m n hm hn
      have hle : c₁ * d₁ (u m) (u n) ≤ d₂ (u m) (u n) := (hbound _ _).1
      have hdn : d₂ (u m) (u n) < c₁ * ε := hN m n hm hn
      have : d₁ (u m) (u n) < ε := by
        have : c₁ * d₁ (u m) (u n) < c₁ * ε := lt_of_le_of_lt hle hdn
        exact (lt_of_mul_lt_mul_left this (le_of_lt hc₁))
      exact this
    · intro hu ε hεpos
      have hεpos' : 0 < ε / c₂ := div_pos hεpos hc₂
      rcases hu (ε / c₂) hεpos' with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro m n hm hn
      have hle : d₂ (u m) (u n) ≤ c₂ * d₁ (u m) (u n) := (hbound _ _).2
      have hdn : d₁ (u m) (u n) < ε / c₂ := hN m n hm hn
      have : d₂ (u m) (u n) < ε := by
        have h := mul_lt_mul_of_pos_left hdn hc₂
        have hc₂ne : c₂ ≠ 0 := ne_of_gt hc₂
        have h' : c₂ * (ε / c₂) = ε := by field_simp [hc₂ne]
        exact lt_of_le_of_lt hle (by simpa [h'] using h)
      exact this
  exact ⟨hopen, hclosed, hcauchy⟩

/-- Text 15.0.19: Since `C` is bounded and `0 ∈ int C`, there exist `α, β > 0` such that
`α B ⊆ C ⊆ β B`, where `B` is the Euclidean unit ball.

Writing `d(x,y) = ‖x - y‖₂`, the associated Minkowski metric `ρ` satisfies the two-sided comparison
`α^{-1} d(x,y) ≥ ρ(x,y) ≥ β^{-1} d(x,y)` for all `x,y`.

Consequently, Minkowski metrics on `ℝⁿ` are topologically equivalent to the Euclidean metric: they
induce the same open/closed sets and the same Cauchy sequences. -/
theorem exists_constants_unitBall_sandwich_and_topologicalEquiv_of_minkowskiMetricFun_ball_eq
    {n : ℕ} {C : Set (Fin n → ℝ)} {ρ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hρ : IsMinkowskiMetricFun ρ) (hC_bdd : Bornology.IsBounded C)
    (hC0 : (0 : Fin n → ℝ) ∈ interior C)
    (hball : ∀ x : Fin n → ℝ, ∀ ε : ℝ, 0 < ε → {y | ρ x y ≤ ε} = (fun c => x + ε • c) '' C) :
    ∃ α β : ℝ,
      0 < α ∧
        0 < β ∧
          ((fun x => α • x) '' piEuclideanUnitBall n ⊆ C) ∧
            (C ⊆ (fun x => β • x) '' piEuclideanUnitBall n) ∧
              (∀ x y : Fin n → ℝ,
                  β⁻¹ * piEuclideanDist x y ≤ ρ x y ∧ ρ x y ≤ α⁻¹ * piEuclideanDist x y) ∧
                (∀ s : Set (Fin n → ℝ),
                    IsOpenOfDistFun ρ s ↔ IsOpenOfDistFun (piEuclideanDist (n := n)) s) ∧
                (∀ s : Set (Fin n → ℝ),
                    IsClosedOfDistFun ρ s ↔ IsClosedOfDistFun (piEuclideanDist (n := n)) s) ∧
                    ∀ u : ℕ → Fin n → ℝ,
                      CauchySeqOfDistFun ρ u ↔
                        CauchySeqOfDistFun (piEuclideanDist (n := n)) u := by
  have hmetric : IsMetricFun ρ := hρ.1
  rcases hmetric with ⟨hρpos, hρdiag, _hsymm, _htri⟩
  rcases exists_pos_smul_piEuclideanUnitBall_subset_of_zero_mem_interior (n := n) (C := C) hC0 with
    ⟨α, hαpos, hCα⟩
  rcases exists_pos_smul_piEuclideanUnitBall_superset_of_isBounded (n := n) (C := C) hC_bdd with
    ⟨β, hβpos, hCβ⟩
  have hbounds :
      ∀ x y : Fin n → ℝ,
        β⁻¹ * piEuclideanDist x y ≤ ρ x y ∧ ρ x y ≤ α⁻¹ * piEuclideanDist x y :=
    rho_bounds_of_ball_eq_and_unitBall_sandwich (n := n) (C := C) (ρ := ρ) (α := α) (β := β)
      hαpos hβpos hCα hCβ hρdiag hρpos hball
  have htop :
      (∀ s : Set (Fin n → ℝ),
          IsOpenOfDistFun ρ s ↔ IsOpenOfDistFun (piEuclideanDist (n := n)) s) ∧
        (∀ s : Set (Fin n → ℝ),
          IsClosedOfDistFun ρ s ↔ IsClosedOfDistFun (piEuclideanDist (n := n)) s) ∧
          (∀ u : ℕ → Fin n → ℝ,
            CauchySeqOfDistFun ρ u ↔
              CauchySeqOfDistFun (piEuclideanDist (n := n)) u) := by
    have hposβ : 0 < β⁻¹ := inv_pos.mpr hβpos
    have hposα : 0 < α⁻¹ := inv_pos.mpr hαpos
    exact
      isOpen_isClosed_cauchy_equiv_of_two_sided_bounds (α := Fin n → ℝ)
        (d₁ := piEuclideanDist (n := n)) (d₂ := ρ)
        (c₁ := β⁻¹) (c₂ := α⁻¹) hposβ hposα hbounds
  refine ⟨α, β, hαpos, hβpos, hCα, hCβ, hbounds, ?_, ?_, ?_⟩
  · exact htop.1
  · exact htop.2.1
  · exact htop.2.2

/-- Text 15.0.20: An extended-real-valued convex function `f : ℝⁿ → (-∞, +∞]` is *gauge-like* if
`f(0) = inf f` and all its sublevel sets `{x | f x ≤ α}` for `f(0) < α < +∞` are proportional, i.e.
each is a positive scalar multiple of any other such sublevel set. -/
def IsGaugeLike {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  ConvexFunctionOn (S := (Set.univ : Set (Fin n → ℝ))) f ∧
    f 0 = sInf (Set.range f) ∧
      ∀ ⦃α β : EReal⦄,
        f 0 < α → α < ⊤ → f 0 < β → β < ⊤ →
          ∃ t : ℝ, 0 < t ∧ {x | f x ≤ α} = t • {x | f x ≤ β}

/-- Sublevel sets of a gauge-like function are homothetic. -/
lemma sublevel_sets_homothetic_of_IsGaugeLike {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : IsGaugeLike f) {α β : EReal} (hα0 : f 0 < α) (hαtop : α < ⊤)
    (hβ0 : f 0 < β) (hβtop : β < ⊤) :
    ∃ t : ℝ, 0 < t ∧ {x | f x ≤ α} = t • {x | f x ≤ β} := by
  rcases hf with ⟨_hconv, _hmin, hhom⟩
  exact hhom hα0 hαtop hβ0 hβtop

/-- Sublevel sets of a gauge scale by positive factors. -/
lemma sublevel_eq_smul_sublevel_one_of_isGauge {n : ℕ} {k : (Fin n → ℝ) → EReal}
    (hk : IsGauge k) {t : ℝ} (ht : 0 < t) :
    {x | k x ≤ (t : EReal)} = t • {x | k x ≤ (1 : EReal)} := by
  classical
  ext x
  constructor
  · intro hx
    refine ⟨(t⁻¹) • x, ?_, ?_⟩
    · have hhom :
        k (t⁻¹ • x) = ((t⁻¹ : ℝ) : EReal) * k x :=
        hk.2.2.1 x t⁻¹ (le_of_lt (inv_pos.mpr ht))
      have hx' : k x ≤ (t : EReal) := by simpa using hx
      have hmul :
          ((t⁻¹ : ℝ) : EReal) * k x ≤ ((t⁻¹ : ℝ) : EReal) * (t : EReal) := by
        refine mul_le_mul_of_nonneg_left hx' ?_
        exact_mod_cast (le_of_lt (inv_pos.mpr ht))
      have htne : t ≠ 0 := ne_of_gt ht
      have hmul' : ((t⁻¹ : ℝ) : EReal) * (t : EReal) = (1 : EReal) := by
        calc
          ((t⁻¹ : ℝ) : EReal) * (t : EReal) = ((t⁻¹ * t : ℝ) : EReal) := by
            simp [EReal.coe_mul]
          _ = (1 : EReal) := by
            have : (t⁻¹ * t : ℝ) = 1 := by field_simp [htne]
            simp [this]
      have hx1 : k (t⁻¹ • x) ≤ (1 : EReal) := by
        have : ((t⁻¹ : ℝ) : EReal) * k x ≤ (1 : EReal) := by
          calc
            ((t⁻¹ : ℝ) : EReal) * k x ≤ ((t⁻¹ : ℝ) : EReal) * (t : EReal) := hmul
            _ = (1 : EReal) := hmul'
        simpa [hhom] using this
      exact hx1
    · have htne : t ≠ 0 := ne_of_gt ht
      calc
        t • (t⁻¹ • x) = (t * t⁻¹) • x := by simp [smul_smul]
        _ = (1 : ℝ) • x := by simp [htne]
        _ = x := by simp
  · rintro ⟨y, hy, rfl⟩
    have hhom : k (t • y) = ((t : ℝ) : EReal) * k y :=
      hk.2.2.1 y t (le_of_lt ht)
    have hy' : k y ≤ (1 : EReal) := by simpa using hy
    have hmul :
        ((t : ℝ) : EReal) * k y ≤ ((t : ℝ) : EReal) * (1 : EReal) := by
      refine mul_le_mul_of_nonneg_left hy' ?_
      exact_mod_cast (le_of_lt ht)
    have hmul' : ((t : ℝ) : EReal) * (1 : EReal) = (t : EReal) := by
      simp
    simpa [hhom, hmul'] using hmul

/-- A gauge taking a positive finite value attains `1` on some point. -/
lemma exists_unit_level_of_pos_finite {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k) :
    (∃ y : Fin n → ℝ, (0 : EReal) < k y ∧ k y < ⊤) → ∃ y1 : Fin n → ℝ, k y1 = (1 : EReal) := by
  rintro ⟨y, hypos, hytop⟩
  have hybot : k y ≠ (⊥ : EReal) := IsGauge.ne_bot hk y
  set r : ℝ := (k y).toReal
  have hco : (r : EReal) = k y := by
    have hytop' : k y ≠ ⊤ := ne_of_lt hytop
    simpa [r] using (EReal.coe_toReal (x := k y) hytop' hybot)
  have hrpos : 0 < r := by
    have : (0 : EReal) < (r : EReal) := by simpa [hco] using hypos
    exact (EReal.coe_lt_coe_iff.mp this)
  refine ⟨(r⁻¹) • y, ?_⟩
  have hhom : k (r⁻¹ • y) = ((r⁻¹ : ℝ) : EReal) * k y :=
    hk.2.2.1 y r⁻¹ (le_of_lt (inv_pos.mpr hrpos))
  have hmul : ((r⁻¹ : ℝ) : EReal) * k y = (1 : EReal) := by
    have hrne : r ≠ 0 := ne_of_gt hrpos
    calc
      ((r⁻¹ : ℝ) : EReal) * k y = ((r⁻¹ : ℝ) : EReal) * (r : EReal) := by
        simp [hco]
      _ = ((r⁻¹ * r : ℝ) : EReal) := by
        simp [EReal.coe_mul]
      _ = (1 : EReal) := by
        have : (r⁻¹ * r : ℝ) = 1 := by field_simp [hrne]
        simp [this]
  simp [hhom, hmul]

/-- The support function of a nonempty convex set containing `0` is a gauge. -/
lemma supportFunctionEReal_isGauge_of_convex_zeroMem {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCne : C.Nonempty) (hCconv : Convex ℝ C) (hC0 : (0 : Fin n → ℝ) ∈ C) :
    IsGauge (supportFunctionEReal C) := by
  have hclosed :
      ClosedConvexFunction (supportFunctionEReal C) :=
    (section13_supportFunctionEReal_closedProperConvex_posHom (n := n) (C := C) hCne hCconv).1
  have hpos :
      PositivelyHomogeneous (supportFunctionEReal C) :=
    (section13_supportFunctionEReal_closedProperConvex_posHom (n := n) (C := C) hCne hCconv).2.2
  have hconv_on :
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → ℝ))) (supportFunctionEReal C) := by
    simpa [ConvexFunction] using hclosed.1
  have hnonneg : ∀ xStar, (0 : EReal) ≤ supportFunctionEReal C xStar := by
    intro xStar
    unfold supportFunctionEReal
    have hmem :
        (0 : EReal) ∈
          {z : EReal | ∃ x ∈ C, z = ((dotProduct x xStar : ℝ) : EReal)} := by
      refine ⟨0, hC0, ?_⟩
      simp
    exact le_sSup hmem
  have hzero : supportFunctionEReal C 0 = 0 := by
    have hset0 : {z : EReal | (∃ x, x ∈ C) ∧ z = 0} = ({0} : Set EReal) := by
      ext z
      constructor
      · rintro ⟨⟨x, _hxC⟩, rfl⟩
        simp
      · intro hz
        refine ⟨⟨0, hC0⟩, ?_⟩
        simpa [hz]
    simp [supportFunctionEReal, hset0]
  have hhom :
      ∀ xStar (r : ℝ), 0 ≤ r →
        supportFunctionEReal C (r • xStar) =
          ((r : ℝ) : EReal) * supportFunctionEReal C xStar := by
    intro xStar r hr
    by_cases hr0 : r = 0
    · subst hr0
      simp [hzero]
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      simpa using (hpos xStar r hrpos)
  exact ⟨hconv_on, hnonneg, hhom, hzero⟩

/-- A gauge is *closed* if its epigraph over `univ` is closed. -/
def IsClosedGauge {n : ℕ} (k : (Fin n → ℝ) → EReal) : Prop :=
  IsGauge k ∧ IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k)

/-- The support function of a nonempty convex set containing `0` is a closed gauge. -/
lemma supportFunctionEReal_isClosedGauge_of_convex_zeroMem {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCne : C.Nonempty) (hCconv : Convex ℝ C) (hC0 : (0 : Fin n → ℝ) ∈ C) :
    IsClosedGauge (supportFunctionEReal C) := by
  have hk : IsGauge (supportFunctionEReal C) :=
    supportFunctionEReal_isGauge_of_convex_zeroMem (C := C) hCne hCconv hC0
  have hclosed :
      ClosedConvexFunction (supportFunctionEReal C) :=
    (section13_supportFunctionEReal_closedProperConvex_posHom (n := n) (C := C) hCne hCconv).1
  have hls : LowerSemicontinuous (supportFunctionEReal C) := hclosed.2
  have hsub :
      ∀ α : ℝ, IsClosed {x | supportFunctionEReal C x ≤ (α : EReal)} :=
    (lowerSemicontinuous_iff_closed_sublevel (f := supportFunctionEReal C)).1 hls
  have hclosed_epi :
      IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) (supportFunctionEReal C)) :=
    closed_epigraph_of_closed_sublevel (f := supportFunctionEReal C) hsub
  exact ⟨hk, hclosed_epi⟩

/-- The support function of a set containing `0` is nonnegative. -/
lemma supportFunctionEReal_nonneg_of_zero_mem {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC0 : (0 : Fin n → ℝ) ∈ C) (xStar : Fin n → ℝ) :
    (0 : EReal) ≤ supportFunctionEReal C xStar := by
  unfold supportFunctionEReal
  have hmem :
      (0 : EReal) ∈
        {z : EReal | ∃ x ∈ C, z = ((dotProduct x xStar : ℝ) : EReal)} := by
    refine ⟨0, hC0, ?_⟩
    simp
  exact le_sSup hmem

/-- A function is *gauge-like closed proper convex* if it is gauge-like and is a closed proper
convex `EReal`-valued function on `ℝⁿ` (modeled as `Fin n → ℝ`). -/
def IsGaugeLikeClosedProperConvex {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  IsGaugeLike f ∧ ClosedConvexFunction f ∧
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f

/-- A gauge-like closed proper convex function has a finite level strictly above `f 0`. -/
lemma exists_real_beta_between_f0_and_top {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : IsGaugeLikeClosedProperConvex f) :
    ∃ β : ℝ, f 0 < (β : EReal) ∧ (β : EReal) < ⊤ := by
  classical
  rcases hf with ⟨hgl, _hclosed, hproper⟩
  rcases hgl with ⟨_hconv, hmin, _hhom⟩
  rcases hproper with ⟨_hconv', hne_epi, hne_bot⟩
  rcases hne_epi with ⟨⟨x0, μ⟩, hx0⟩
  have hx0_le : f x0 ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := f)).1 hx0
  have hx0_ne_top : f x0 ≠ ⊤ := by
    intro htop
    have hx0_le' := hx0_le
    rw [htop] at hx0_le'
    exact (not_top_le_coe μ) hx0_le'
  have h0_le_fx0 : f 0 ≤ f x0 := by
    have hx0mem : f x0 ∈ Set.range f := ⟨x0, rfl⟩
    have hle : sInf (Set.range f) ≤ f x0 := sInf_le hx0mem
    simpa [hmin] using hle
  have h0_ne_top : f 0 ≠ ⊤ := by
    intro h0top
    have : (⊤ : EReal) ≤ f x0 := by simpa [h0top] using h0_le_fx0
    exact hx0_ne_top (top_le_iff.mp this)
  have h0_ne_bot : f 0 ≠ ⊥ := by
    exact hne_bot 0 (by simp)
  set r : ℝ := (f 0).toReal
  have hco : (r : EReal) = f 0 := by
    simpa [r] using (EReal.coe_toReal (x := f 0) h0_ne_top h0_ne_bot)
  refine ⟨r + 1, ?_, ?_⟩
  · have : (r : EReal) < ((r + 1) : EReal) := by
      exact (EReal.coe_lt_coe_iff).2 (by linarith)
    simpa [hco] using this
  · simpa using (EReal.coe_lt_top (r + 1))

/-- Sublevel sets of a closed convex function are closed and convex. -/
lemma sublevel_closed_convex_of_closedConvex {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : ClosedConvexFunction f) (α : ℝ) :
    IsClosed {x | f x ≤ (α : EReal)} ∧ Convex ℝ {x | f x ≤ (α : EReal)} := by
  have hclosed :
      IsClosed {x | f x ≤ (α : EReal)} :=
    (lowerSemicontinuous_iff_closed_sublevel (f := f)).1 hf.2 α
  have hconv_epi :
      Convex ℝ (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
    simpa [ConvexFunction] using hf.1
  have hconv : Convex ℝ {x | f x ≤ (α : EReal)} := by
    refine (convex_iff_add_mem).2 ?_
    intro x hx y hy a b ha hb hab
    have hx' : f x ≤ (α : EReal) := by simpa using hx
    have hy' : f y ≤ (α : EReal) := by simpa using hy
    have hxmem : x ∈ (Set.univ : Set (Fin n → ℝ)) := by simp
    have hymem : y ∈ (Set.univ : Set (Fin n → ℝ)) := by simp
    have hb1 : b ≤ 1 := by nlinarith [hab, ha]
    have hle' :
        f ((1 - b) • x + b • y) ≤ (((1 - b) * α + b * α : ℝ) : EReal) :=
      epigraph_combo_ineq_aux (S := (Set.univ : Set (Fin n → ℝ))) (f := f)
        hconv_epi hxmem hymem hx' hy' hb hb1
    have hcomb : (1 - b) = a := by nlinarith [hab]
    have hle :
        f (a • x + b • y) ≤ ((a * α + b * α : ℝ) : EReal) := by
      simpa [hcomb] using hle'
    have hcomb2 : (a * α + b * α : ℝ) = α := by
      calc
        a * α + b * α = (a + b) * α := by ring
        _ = α := by simp [hab]
    simpa [hcomb2] using hle
  exact ⟨hclosed, hconv⟩

/-- The bipolar set always contains the original set. -/
lemma subset_bipolar_of_any {n : ℕ} {C : Set (Fin n → ℝ)} :
    C ⊆
      {x | ∀ xStar ∈ {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1},
        (x ⬝ᵥ xStar : ℝ) ≤ 1} := by
  intro x hx xStar hxStar
  exact hxStar x hx

/-- Any linear functional on `Fin n → ℝ` is a dot product with its coordinates on the standard basis. -/
lemma linearMap_eq_dotProduct_piSingle {n : ℕ} (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) :
    ∀ x, f x = (x ⬝ᵥ fun i => f (Pi.single i 1) : ℝ) := by
  classical
  intro x
  have hx : ∑ i : Fin n, x i • (Pi.single i (1 : ℝ) : Fin n → ℝ) = x := by
    simpa [Pi.basisFun_apply] using (Pi.basisFun ℝ (Fin n)).sum_repr x
  have hx' : x = ∑ i : Fin n, x i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := hx.symm
  calc
    f x = f (∑ i : Fin n, x i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
      simpa using (congrArg f hx).symm
    _ = ∑ i : Fin n, f (x i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
      simp
    _ = ∑ i : Fin n, x i * f (Pi.single i (1 : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp [smul_eq_mul]
    _ = (x ⬝ᵥ fun i => f (Pi.single i (1 : ℝ)) : ℝ) := by
      simp [dotProduct]

/-- A closed convex set containing `0` coincides with its bipolar. -/
lemma bipolar_eq_of_closed_convex_zeroMem {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hCconv : Convex ℝ C) (hC0 : (0 : Fin n → ℝ) ∈ C) :
    C =
      {x | ∀ xStar ∈ {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1},
        (x ⬝ᵥ xStar : ℝ) ≤ 1} := by
  ext x
  constructor
  · intro hx
    exact subset_bipolar_of_any (C := C) hx
  · intro hx
    have hbip :
        {x : Fin n → ℝ | ∀ φ ∈ polar (E := Fin n → ℝ) C, φ x ≤ 1} = C :=
      section14_bipolar_eq_of_closed_convex (E := Fin n → ℝ) hCclosed hCconv hC0
    have hx' :
        x ∈ {x : Fin n → ℝ | ∀ φ ∈ polar (E := Fin n → ℝ) C, φ x ≤ 1} := by
      intro φ hφ
      let xStar : Fin n → ℝ := fun i => φ (Pi.single i 1)
      have hxStar :
          xStar ∈ {xStar | ∀ y ∈ C, (y ⬝ᵥ xStar : ℝ) ≤ 1} := by
        intro y hy
        have hyφ : φ y ≤ 1 := (mem_polar_iff (E := Fin n → ℝ) (C := C) (φ := φ)).1 hφ y hy
        have hφy : φ y = (y ⬝ᵥ xStar : ℝ) := by
          simpa [xStar] using (linearMap_eq_dotProduct_piSingle (f := φ) y)
        simpa [hφy] using hyφ
      have hxle : (x ⬝ᵥ xStar : ℝ) ≤ 1 := hx xStar hxStar
      have hφx : φ x = (x ⬝ᵥ xStar : ℝ) := by
        simpa [xStar] using (linearMap_eq_dotProduct_piSingle (f := φ) x)
      simpa [hφx] using hxle
    simpa [hbip] using hx'

/-- Build a closed gauge from a base sublevel of a gauge-like closed proper convex function. -/
lemma closedGauge_from_baseSublevel_supportFunctionEReal_polar_and_unitSublevel {n : ℕ}
    {f : (Fin n → ℝ) → EReal} {β : ℝ}
    (hf : IsGaugeLikeClosedProperConvex f)
    (hβ0 : f 0 < (β : EReal)) :
    let C : Set (Fin n → ℝ) := {x | f x ≤ (β : EReal)}
    let Cpolar : Set (Fin n → ℝ) := {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1}
    let k : (Fin n → ℝ) → EReal := supportFunctionEReal Cpolar
    IsClosedGauge k ∧ {x | k x ≤ (1 : EReal)} = C := by
  classical
  set C : Set (Fin n → ℝ) := {x | f x ≤ (β : EReal)}
  set Cpolar : Set (Fin n → ℝ) := {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1}
  set k : (Fin n → ℝ) → EReal := supportFunctionEReal Cpolar
  have hCclosedconv : IsClosed C ∧ Convex ℝ C := by
    simpa [C] using (sublevel_closed_convex_of_closedConvex (f := f) (α := β) hf.2.1)
  have hC0 : (0 : Fin n → ℝ) ∈ C := by
    have : f 0 ≤ (β : EReal) := le_of_lt hβ0
    simpa [C] using this
  have hCpolar0 : (0 : Fin n → ℝ) ∈ Cpolar := by
    intro x hx
    simp
  have hCpolarne : Cpolar.Nonempty := ⟨0, hCpolar0⟩
  have hCpolarconv : Convex ℝ Cpolar := by
    intro x hx y hy a b ha hb hab
    intro z hz
    have hxz : (z ⬝ᵥ x : ℝ) ≤ 1 := hx z hz
    have hyz : (z ⬝ᵥ y : ℝ) ≤ 1 := hy z hz
    have hdot :
        (z ⬝ᵥ (a • x + b • y) : ℝ) =
          a * (z ⬝ᵥ x : ℝ) + b * (z ⬝ᵥ y : ℝ) := by
      simp [dotProduct_add, dotProduct_smul, smul_eq_mul]
    have hle :
        a * (z ⬝ᵥ x : ℝ) + b * (z ⬝ᵥ y : ℝ) ≤ a * 1 + b * 1 := by
      nlinarith [hxz, hyz, ha, hb]
    have hle' : a * 1 + b * 1 ≤ (1 : ℝ) := by nlinarith [hab]
    exact le_trans (by simpa [hdot] using hle) hle'
  have hk : IsClosedGauge k :=
    supportFunctionEReal_isClosedGauge_of_convex_zeroMem (C := Cpolar) hCpolarne hCpolarconv
      hCpolar0
  have hsub :
      {x | k x ≤ (1 : EReal)} =
        {x | ∀ xStar ∈ Cpolar, (xStar ⬝ᵥ x : ℝ) ≤ 1} := by
    simpa [k] using (supportFunctionEReal_sublevel_one_eq_polarSet (C := Cpolar))
  have hsub' :
      {x | k x ≤ (1 : EReal)} =
        {x | ∀ xStar ∈ Cpolar, (x ⬝ᵥ xStar : ℝ) ≤ 1} := by
    ext x
    constructor
    · intro hx xStar hxStar
      have hx' :
          ∀ y ∈ Cpolar, (y ⬝ᵥ x : ℝ) ≤ 1 := by simpa [hsub] using hx
      simpa [dotProduct_comm] using hx' xStar hxStar
    · intro hx
      have hx' :
          ∀ y ∈ Cpolar, (x ⬝ᵥ y : ℝ) ≤ 1 := by simpa using hx
      have hx'' : ∀ y ∈ Cpolar, (y ⬝ᵥ x : ℝ) ≤ 1 := by
        intro y hy
        simpa [dotProduct_comm] using hx' y hy
      simpa [hsub] using hx''
  have hCeq : C = {x | ∀ xStar ∈ Cpolar, (x ⬝ᵥ xStar : ℝ) ≤ 1} := by
    simpa [Cpolar] using
      (bipolar_eq_of_closed_convex_zeroMem (C := C) hCclosedconv.1 hCclosedconv.2 hC0)
  refine ⟨hk, ?_⟩
  exact hsub'.trans hCeq.symm

/-- Pick a base sublevel and a closed gauge whose unit sublevel matches it. -/
lemma exists_closedGauge_unitSublevel_eq_baseSublevel {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : IsGaugeLikeClosedProperConvex f) :
    ∃ β : ℝ, f 0 < (β : EReal) ∧ (β : EReal) < ⊤ ∧
      ∃ k : (Fin n → ℝ) → EReal, IsClosedGauge k ∧
        {x | k x ≤ (1 : EReal)} = {x | f x ≤ (β : EReal)} := by
  classical
  rcases exists_real_beta_between_f0_and_top (f := f) hf with ⟨β, hβ0, hβtop⟩
  set C : Set (Fin n → ℝ) := {x | f x ≤ (β : EReal)}
  set Cpolar : Set (Fin n → ℝ) := {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1}
  set k : (Fin n → ℝ) → EReal := supportFunctionEReal Cpolar
  have hk' :
      IsClosedGauge k ∧ {x | k x ≤ (1 : EReal)} = C := by
    simpa [C, Cpolar, k] using
      (closedGauge_from_baseSublevel_supportFunctionEReal_polar_and_unitSublevel (f := f) (β := β)
        hf hβ0)
  refine ⟨β, hβ0, hβtop, k, hk'.1, ?_⟩
  simpa [C] using hk'.2

/-- The support function of the unit sublevel of a gauge is bounded by its polar gauge. -/
lemma supportFunction_unitSublevel_le_polarGauge_of_isGauge {n : ℕ} {k : (Fin n → ℝ) → EReal}
    (xStar : Fin n → ℝ) :
    supportFunctionEReal {x | k x ≤ (1 : EReal)} xStar ≤ polarGauge k xStar := by
  unfold polarGauge
  refine le_sInf ?_
  intro μ hμ
  rcases hμ with ⟨hμ0, hμ⟩
  unfold supportFunctionEReal
  refine sSup_le ?_
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  have hxk : k x ≤ (1 : EReal) := by simpa using hx
  have hdot : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ μ * k x := hμ x
  have hmul : μ * k x ≤ μ := by
    have hmul' : μ * k x ≤ μ * (1 : EReal) :=
      mul_le_mul_of_nonneg_left hxk hμ0
    simpa using hmul'
  exact hdot.trans hmul

/-- If the unit-sublevel support function is finite, then any `x` with `k x = 0` pairs
nonpositively with the dual vector. -/
lemma dotProduct_le_zero_of_k_eq_zero_of_supportFunction_ne_top {n : ℕ}
    {k : (Fin n → ℝ) → EReal} (hk : IsGauge k) {xStar : Fin n → ℝ}
    (hμtop : supportFunctionEReal {x | k x ≤ (1 : EReal)} xStar ≠ ⊤)
    {x : Fin n → ℝ} (hx0 : k x = 0) :
    ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ 0 := by
  classical
  set C : Set (Fin n → ℝ) := {x | k x ≤ (1 : EReal)}
  set μ : EReal := supportFunctionEReal C xStar
  have hC0 : (0 : Fin n → ℝ) ∈ C := by
    have hk0 : k 0 = 0 := hk.2.2.2
    have : k 0 ≤ (1 : EReal) := by simp [hk0]
    simpa [C] using this
  have hμ_nonneg : (0 : EReal) ≤ μ :=
    supportFunctionEReal_nonneg_of_zero_mem (C := C) hC0 xStar
  have hμtop' : μ ≠ ⊤ := by simpa [μ, C] using hμtop
  have hμ_le_real : μ ≤ (μ.toReal : EReal) := EReal.le_coe_toReal (x := μ) hμtop'
  have hdot_le_mu : ∀ y ∈ C, ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ μ := by
    intro y hy
    unfold μ supportFunctionEReal
    refine le_sSup ?_
    exact ⟨y, hy, rfl⟩
  by_contra hpos
  have hpos' : (0 : EReal) < ((x ⬝ᵥ xStar : ℝ) : EReal) := lt_of_not_ge hpos
  have hpos_real : 0 < (x ⬝ᵥ xStar : ℝ) := (EReal.coe_lt_coe_iff).1 hpos'
  set t : ℝ := μ.toReal / (x ⬝ᵥ xStar : ℝ) + 1
  have hμ_real_nonneg : 0 ≤ μ.toReal := EReal.toReal_nonneg hμ_nonneg
  have htpos : 0 < t := by
    have hfrac_nonneg : 0 ≤ μ.toReal / (x ⬝ᵥ xStar : ℝ) :=
      div_nonneg hμ_real_nonneg (le_of_lt hpos_real)
    have : 0 < μ.toReal / (x ⬝ᵥ xStar : ℝ) + 1 := by linarith
    simpa [t] using this
  have hxC : t • x ∈ C := by
    have hhom : k (t • x) = ((t : ℝ) : EReal) * k x :=
      hk.2.2.1 x t (le_of_lt htpos)
    have hzero : k (t • x) = 0 := by simpa [hx0] using hhom
    have hle : k (t • x) ≤ (1 : EReal) := by simp [hzero]
    simpa [C] using hle
  have hdot_le : ((dotProduct (t • x) xStar : ℝ) : EReal) ≤ μ := hdot_le_mu _ hxC
  have hdot_gt_real : μ.toReal < t * (x ⬝ᵥ xStar : ℝ) := by
    have hd_ne : (x ⬝ᵥ xStar : ℝ) ≠ 0 := ne_of_gt hpos_real
    have hmul :
        t * (x ⬝ᵥ xStar : ℝ) = μ.toReal + (x ⬝ᵥ xStar : ℝ) := by
      dsimp [t]
      field_simp [hd_ne]
    have : μ.toReal < μ.toReal + (x ⬝ᵥ xStar : ℝ) := by linarith [hpos_real]
    simpa [hmul] using this
  have hdot_gt : (μ.toReal : EReal) < ((dotProduct (t • x) xStar : ℝ) : EReal) := by
    have hdot_eq : dotProduct (t • x) xStar = t * (x ⬝ᵥ xStar : ℝ) := by
      simp [smul_dotProduct]
    have : (μ.toReal : EReal) < (t * (x ⬝ᵥ xStar : ℝ) : EReal) :=
      (EReal.coe_lt_coe_iff).2 hdot_gt_real
    simpa [hdot_eq] using this
  have hμ_lt : μ < ((dotProduct (t • x) xStar : ℝ) : EReal) :=
    lt_of_le_of_lt hμ_le_real hdot_gt
  exact (not_lt_of_ge hdot_le) hμ_lt

end Section15
end Chap03
