/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
  -/

import Mathlib

section Chap03
section Section07

/-- The sequence of functions `f_n(x) = n^{-1/2} sin(n x)` on `ℝ`. -/
noncomputable def sinScaledSeq (n : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ * Real.sin ((n : ℝ) * x)

/-- The constant zero function on `ℝ`. -/
def sinScaledLimit : ℝ → ℝ := fun _ => 0

/-- Helper for Proposition 3.19: for any `ε>0`, eventually `1/√n < ε`. -/
lemma helperForProposition_3_19_eventually_inv_sqrt_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, (Real.sqrt (n : ℝ))⁻¹ < ε := by
  have hposinv : 0 < ε⁻¹ := inv_pos.mpr hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (ε⁻¹) ^ 2 < (N : ℝ) := by
    exact exists_nat_gt ((ε⁻¹) ^ 2)
  refine Filter.eventually_atTop.2 ?_
  refine ⟨N, ?_⟩
  intro n hn
  have hN' : (ε⁻¹) ^ 2 < (n : ℝ) := by
    have hNle : (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    exact lt_of_lt_of_le hN hNle
  have hsqrt : ε⁻¹ < Real.sqrt (n : ℝ) := by
    have hsqrt' : Real.sqrt ((ε⁻¹) ^ 2) < Real.sqrt (n : ℝ) := by
      exact Real.sqrt_lt_sqrt (sq_nonneg (ε⁻¹)) hN'
    have hsqrt'' : |ε⁻¹| < Real.sqrt (n : ℝ) := by
      calc
        |ε⁻¹| = Real.sqrt ((ε⁻¹) ^ 2) := by
          symm
          exact Real.sqrt_sq_eq_abs (ε⁻¹)
        _ < Real.sqrt (n : ℝ) := hsqrt'
    simpa [abs_of_pos hposinv] using hsqrt''
  have hpossqrt : 0 < Real.sqrt (n : ℝ) := by
    have hnpos : 0 < (n : ℝ) := by
      exact lt_of_le_of_lt (sq_nonneg (ε⁻¹)) hN'
    exact (Real.sqrt_pos).2 hnpos
  exact (inv_lt_comm₀ hpossqrt hε).2 hsqrt

/-- Helper for Proposition 3.19: uniform bound for the scaled sine sequence. -/
lemma helperForProposition_3_19_norm_sinScaledSeq_le_inv_sqrt (n : ℕ) (x : ℝ) :
    ‖sinScaledSeq n x - sinScaledLimit x‖ ≤ (Real.sqrt (n : ℝ))⁻¹ := by
  have hsin : ‖Real.sin ((n : ℝ) * x)‖ ≤ (1 : ℝ) := by
    simpa [Real.norm_eq_abs] using (Real.abs_sin_le_one ((n : ℝ) * x))
  have hnonneg : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ := by
    exact (inv_nonneg).2 (Real.sqrt_nonneg _)
  calc
    ‖sinScaledSeq n x - sinScaledLimit x‖ = ‖sinScaledSeq n x‖ := by
      simp [sinScaledLimit]
    _ = ‖(Real.sqrt (n : ℝ))⁻¹ * Real.sin ((n : ℝ) * x)‖ := by
      simp [sinScaledSeq]
    _ = ‖(Real.sqrt (n : ℝ))⁻¹‖ * ‖Real.sin ((n : ℝ) * x)‖ := by
      simpa [norm_mul]
    _ ≤ ‖(Real.sqrt (n : ℝ))⁻¹‖ * 1 := by
      exact mul_le_mul_of_nonneg_left hsin (norm_nonneg _)
    _ = ‖(Real.sqrt (n : ℝ))⁻¹‖ := by simp
    _ = (Real.sqrt (n : ℝ))⁻¹ := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg]

/-- Helper for Proposition 3.19: derivative of the scaled sine sequence. -/
lemma helperForProposition_3_19_deriv_sinScaledSeq (n : ℕ) (x : ℝ) :
    deriv (sinScaledSeq n) x =
      (Real.sqrt (n : ℝ))⁻¹ * (Real.cos ((n : ℝ) * x) * (n : ℝ)) := by
  have hmul : HasDerivAt (fun y : ℝ => (n : ℝ) * y) (n : ℝ) x := by
    simpa using (hasDerivAt_const_mul (n : ℝ) : HasDerivAt (fun y : ℝ => (n : ℝ) * y) (n : ℝ) x)
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin ((n : ℝ) * y))
        (Real.cos ((n : ℝ) * x) * (n : ℝ)) x := by
    exact (Real.hasDerivAt_sin ((n : ℝ) * x)).comp x hmul
  have hconst :
      HasDerivAt
        (fun y : ℝ => (Real.sqrt (n : ℝ))⁻¹ * Real.sin ((n : ℝ) * y))
        ((Real.sqrt (n : ℝ))⁻¹ * (Real.cos ((n : ℝ) * x) * (n : ℝ))) x := by
    exact hsin.const_mul (Real.sqrt (n : ℝ))⁻¹
  change
      deriv (fun y : ℝ => (Real.sqrt (n : ℝ))⁻¹ * Real.sin ((n : ℝ) * y)) x =
        (Real.sqrt (n : ℝ))⁻¹ * (Real.cos ((n : ℝ) * x) * (n : ℝ))
  exact hconst.deriv

/-- Helper for Proposition 3.19: the derivatives at `0` do not converge to the derivative of the limit. -/
lemma helperForProposition_3_19_not_tendsto_deriv_at_zero :
    ¬ Filter.Tendsto (fun n : ℕ => deriv (sinScaledSeq n) 0) Filter.atTop
        (nhds (deriv sinScaledLimit 0)) := by
  intro h
  have hball :
      ∀ᶠ n in Filter.atTop,
        deriv (sinScaledSeq n) 0 ∈ Metric.ball (deriv sinScaledLimit 0) 1 := by
    have hone_pos : (0 : ℝ) < 1 := by
      norm_num
    have hmem : Metric.ball (deriv sinScaledLimit 0) 1 ∈ nhds (deriv sinScaledLimit 0) := by
      simpa using (Metric.ball_mem_nhds (deriv sinScaledLimit 0) hone_pos)
    exact Filter.Tendsto.eventually_mem h hmem
  rcases Filter.eventually_atTop.1 hball with ⟨N, hN⟩
  have hnorm_ge : ∀ n : ℕ, 1 ≤ n → (1 : ℝ) ≤ ‖deriv (sinScaledSeq n) 0‖ := by
    intro n hn
    have hderiv0 : deriv (sinScaledSeq n) 0 = (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) := by
      simp [helperForProposition_3_19_deriv_sinScaledSeq, mul_comm]
    have hnonneg : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) := by
      have h1 : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ := by
        exact (inv_nonneg).2 (Real.sqrt_nonneg _)
      have h2 : 0 ≤ (n : ℝ) := by
        exact_mod_cast (Nat.zero_le n)
      exact mul_nonneg h1 h2
    have hnpos_nat : 0 < n := by
      exact lt_of_lt_of_le (Nat.succ_pos 0) hn
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast hnpos_nat
    have hne : Real.sqrt (n : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 hnpos)
    have hmul : (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) = Real.sqrt (n : ℝ) := by
      have hnnonneg : 0 ≤ (n : ℝ) := by
        exact_mod_cast (Nat.zero_le n)
      calc
        (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) =
            (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by
              nth_rewrite 2 [← Real.mul_self_sqrt hnnonneg]
              rfl
        _ = ((Real.sqrt (n : ℝ))⁻¹ * Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) := by
              ring
        _ = (1 : ℝ) * Real.sqrt (n : ℝ) := by
              simp [hne]
        _ = Real.sqrt (n : ℝ) := by simp
    have hnorm : ‖deriv (sinScaledSeq n) 0‖ = Real.sqrt (n : ℝ) := by
      calc
        ‖deriv (sinScaledSeq n) 0‖ = ‖(Real.sqrt (n : ℝ))⁻¹ * (n : ℝ)‖ := by
          simpa [hderiv0]
        _ = (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) := by
          simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        _ = Real.sqrt (n : ℝ) := hmul
    have hle : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      have hle' : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hn
      have hle'' : Real.sqrt 1 ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hle'
      simpa [Real.sqrt_one] using hle''
    simpa [hnorm] using hle
  have hmemN :
      deriv (sinScaledSeq (max N 1)) 0 ∈ Metric.ball (deriv sinScaledLimit 0) 1 := by
    exact hN (max N 1) (le_max_left _ _)
  have hnot :
      deriv (sinScaledSeq (max N 1)) 0 ∉ Metric.ball (deriv sinScaledLimit 0) 1 := by
    intro hmem
    have hdist : dist (deriv (sinScaledSeq (max N 1)) 0) (deriv sinScaledLimit 0) < 1 := by
      simpa [Metric.mem_ball] using hmem
    have hge : (1 : ℝ) ≤ dist (deriv (sinScaledSeq (max N 1)) 0) (deriv sinScaledLimit 0) := by
      have hle :
          (1 : ℝ) ≤ ‖deriv (sinScaledSeq (max N 1)) 0‖ := by
        have hmax : 1 ≤ max N 1 := by
          exact le_max_right _ _
        exact hnorm_ge (max N 1) hmax
      have hderiv_limit : deriv sinScaledLimit 0 = 0 := by
        change deriv (fun _ : ℝ => 0) 0 = 0
        exact deriv_const (x := (0 : ℝ)) (c := (0 : ℝ))
      have hdist_eq :
          dist (deriv (sinScaledSeq (max N 1)) 0) (deriv sinScaledLimit 0) =
            ‖deriv (sinScaledSeq (max N 1)) 0‖ := by
        rw [hderiv_limit, dist_eq_norm, sub_zero]
      calc
        (1 : ℝ) ≤ ‖deriv (sinScaledSeq (max N 1)) 0‖ := hle
        _ = dist (deriv (sinScaledSeq (max N 1)) 0) (deriv sinScaledLimit 0) := by
          symm
          exact hdist_eq
    exact (not_lt_of_ge hge) hdist
  exact hnot hmemN

/-- Proposition 3.19: for `f_n(x) = n^{-1/2} sin(n x)` on `[0, 2π]` and `f(x)=0`,
`(f_n)` converges uniformly to `f` on `[0, 2π]`, but `(f_n')` does not converge
pointwise to `f'` (hence not uniformly); in particular, `d/dx (lim f_n) ≠ lim (d/dx f_n)`. -/
theorem proposition_3_19 :
    TendstoUniformlyOn sinScaledSeq sinScaledLimit Filter.atTop
        (Set.Icc (0 : ℝ) (2 * Real.pi)) ∧
      ¬ (∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        Filter.Tendsto (fun n => deriv (sinScaledSeq n) x) Filter.atTop
          (nhds (deriv sinScaledLimit x))) ∧
      ¬ TendstoUniformlyOn (fun n x => deriv (sinScaledSeq n) x) (fun x => deriv sinScaledLimit x)
        Filter.atTop (Set.Icc (0 : ℝ) (2 * Real.pi)) :=
  by
    refine And.intro ?h_uniform ?h_rest
    · intro u hu
      rcases Metric.mem_uniformity_dist.1 hu with ⟨ε, hε, hεu⟩
      have hε' :
          ∀ᶠ n : ℕ in Filter.atTop, (Real.sqrt (n : ℝ))⁻¹ < ε :=
        helperForProposition_3_19_eventually_inv_sqrt_lt hε
      refine hε'.mono ?_
      intro n hn x hx
      apply hεu
      have hbound :
          ‖sinScaledSeq n x - sinScaledLimit x‖ ≤ (Real.sqrt (n : ℝ))⁻¹ :=
        helperForProposition_3_19_norm_sinScaledSeq_le_inv_sqrt n x
      have hdist' :
          dist (sinScaledSeq n x) (sinScaledLimit x) ≤ (Real.sqrt (n : ℝ))⁻¹ := by
        simpa [dist_eq_norm] using hbound
      have hdist :
          dist (sinScaledLimit x) (sinScaledSeq n x) ≤ (Real.sqrt (n : ℝ))⁻¹ := by
        simpa [dist_comm] using hdist'
      exact lt_of_le_of_lt hdist hn
    · refine And.intro ?h_not_pointwise ?h_not_uniform
      · intro hpoint
        have hx0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
          refine ⟨le_rfl, ?_⟩
          have hpi : (0 : ℝ) ≤ Real.pi := by
            exact le_of_lt Real.pi_pos
          have htwo : (0 : ℝ) ≤ (2 : ℝ) := by
            norm_num
          exact mul_nonneg htwo hpi
        exact helperForProposition_3_19_not_tendsto_deriv_at_zero (hpoint 0 hx0)
      · intro huniform
        have hx0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
          refine ⟨le_rfl, ?_⟩
          have hpi : (0 : ℝ) ≤ Real.pi := by
            exact le_of_lt Real.pi_pos
          have htwo : (0 : ℝ) ≤ (2 : ℝ) := by
            norm_num
          exact mul_nonneg htwo hpi
        have hpoint :
            Filter.Tendsto (fun n => deriv (sinScaledSeq n) 0) Filter.atTop
              (nhds (deriv sinScaledLimit 0)) :=
          TendstoUniformlyOn.tendsto_at huniform hx0
        exact helperForProposition_3_19_not_tendsto_deriv_at_zero hpoint

/-- The sequence of functions `f_n(x) = sqrt(1/n^2 + x^2)` on `ℝ`. -/
noncomputable def sqrtShiftedSeq (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (1 / (n : ℝ) ^ 2 + x ^ 2)

/-- The absolute value function on `ℝ`. -/
def absFun : ℝ → ℝ := fun x => |x|

/-- Helper for Proposition 3.20: at `n = 0`, the sequence equals the absolute value. -/
lemma helperForProposition_3_20_sqrtShiftedSeq_zero_eq_absFun :
    sqrtShiftedSeq 0 = absFun := by
  funext x
  simp [sqrtShiftedSeq, absFun, Real.sqrt_sq_eq_abs]

/-- Helper for Proposition 3.20: `absFun` is not differentiable at `0`. -/
lemma helperForProposition_3_20_not_differentiableAt_absFun_zero :
    ¬ DifferentiableAt ℝ absFun 0 := by
  simpa [absFun] using
    (not_differentiableAt_abs_zero : ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0)

/-- Helper for Proposition 3.20: `Set.Icc (-1) 1` is a neighborhood of `0`. -/
lemma helperForProposition_3_20_Icc_mem_nhds_zero :
    Set.Icc (-1 : ℝ) 1 ∈ nhds (0 : ℝ) := by
  have hIoo : Set.Ioo (-1 : ℝ) 1 ∈ nhds (0 : ℝ) := by
    have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by
      constructor <;> norm_num
    exact (isOpen_Ioo.mem_nhds hmem)
  have hsubset : Set.Ioo (-1 : ℝ) 1 ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  exact Filter.mem_of_superset hIoo hsubset

/-- Helper for Proposition 3.20: `absFun` is not differentiable on `[-1,1]`. -/
lemma helperForProposition_3_20_not_differentiableOn_absFun_Icc :
    ¬ DifferentiableOn ℝ absFun (Set.Icc (-1 : ℝ) 1) := by
  intro hdiff
  have hx0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> norm_num
  have hwithin :
      DifferentiableWithinAt ℝ absFun (Set.Icc (-1 : ℝ) 1) 0 :=
    hdiff 0 hx0
  have hAt : DifferentiableAt ℝ absFun 0 :=
    (DifferentiableWithinAt.differentiableAt hwithin
      helperForProposition_3_20_Icc_mem_nhds_zero)
  exact helperForProposition_3_20_not_differentiableAt_absFun_zero hAt

/-- Helper for Proposition 3.20: the sequence is not differentiable on `[-1,1]` at `n = 0`. -/
lemma helperForProposition_3_20_not_differentiableOn_sqrtShiftedSeq_zero :
    ¬ DifferentiableOn ℝ (sqrtShiftedSeq 0) (Set.Icc (-1 : ℝ) 1) := by
  intro hdiff
  have hx0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> norm_num
  have hwithin :
      DifferentiableWithinAt ℝ (sqrtShiftedSeq 0) (Set.Icc (-1 : ℝ) 1) 0 :=
    hdiff 0 hx0
  have hAt : DifferentiableAt ℝ (sqrtShiftedSeq 0) 0 :=
    (DifferentiableWithinAt.differentiableAt hwithin
      helperForProposition_3_20_Icc_mem_nhds_zero)
  have hAt' : DifferentiableAt ℝ absFun 0 := by
    simpa [helperForProposition_3_20_sqrtShiftedSeq_zero_eq_absFun] using hAt
  exact helperForProposition_3_20_not_differentiableAt_absFun_zero hAt'

/-- Helper for Proposition 3.20: the full differentiability claim over all `n` is false. -/
lemma helperForProposition_3_20_not_forall_differentiableOn :
    ¬ (∀ n, DifferentiableOn ℝ (sqrtShiftedSeq n) (Set.Icc (-1 : ℝ) 1)) := by
  intro hdiff
  exact helperForProposition_3_20_not_differentiableOn_sqrtShiftedSeq_zero (hdiff 0)

/-- Helper for Proposition 3.20: for any `ε>0`, eventually `1/n < ε`. -/
lemma helperForProposition_3_20_eventually_inv_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ)⁻¹ < ε := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ε⁻¹ < (N : ℝ) := by
    exact exists_nat_gt (ε⁻¹)
  refine Filter.eventually_atTop.2 ?_
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hNle : (N : ℝ) ≤ (n : ℝ) := by
    have hnN : N ≤ n := by
      exact le_trans (le_max_left _ _) hn
    exact_mod_cast hnN
  have hpos : (0 : ℝ) < (n : ℝ) := by
    have hn1 : (1 : ℕ) ≤ n := by
      exact le_trans (le_max_right _ _) hn
    exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos 0) hn1)
  have hlt : ε⁻¹ < (n : ℝ) := by
    exact lt_of_lt_of_le hN hNle
  exact (inv_lt_comm₀ hpos hε).2 hlt

/-- Helper for Proposition 3.20: for any `ε>0`, eventually `(n+1)⁻¹ < ε`. -/
lemma helperForProposition_3_20_eventually_inv_succ_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ((n + 1 : ℝ)⁻¹ < ε) := by
  rcases Filter.eventually_atTop.1 (helperForProposition_3_20_eventually_inv_lt hε) with ⟨N, hN⟩
  refine Filter.eventually_atTop.2 ?_
  refine ⟨N, ?_⟩
  intro n hn
  have hN' : N ≤ n + 1 := by
    exact le_trans hn (Nat.le_succ n)
  simpa using (hN (n + 1) hN')

/-- Helper for Proposition 3.20: uniform bound for the shifted square-root sequence. -/
lemma helperForProposition_3_20_norm_sqrtShiftedSeq_sub_absFun_le_inv (n : ℕ) (x : ℝ) :
    ‖sqrtShiftedSeq n x - absFun x‖ ≤ (n : ℝ)⁻¹ := by
  have ha : 0 ≤ (1 / (n : ℝ) ^ 2) := by
    have hsq : 0 ≤ (n : ℝ) ^ 2 := by
      exact sq_nonneg (n : ℝ)
    exact (one_div_nonneg).2 hsq
  have hle_abs : |x| ≤ Real.sqrt (1 / (n : ℝ) ^ 2 + x ^ 2) := by
    have hle : x ^ 2 ≤ 1 / (n : ℝ) ^ 2 + x ^ 2 := by
      exact le_add_of_nonneg_left ha
    calc
      |x| = Real.sqrt (x ^ 2) := by
        symm
        exact Real.sqrt_sq_eq_abs x
      _ ≤ Real.sqrt (1 / (n : ℝ) ^ 2 + x ^ 2) := by
        exact Real.sqrt_le_sqrt hle
  have hnonneg : 0 ≤ Real.sqrt (1 / (n : ℝ) ^ 2 + x ^ 2) - |x| := by
    exact sub_nonneg.mpr hle_abs
  have hle_sqrt :
      Real.sqrt (1 / (n : ℝ) ^ 2 + x ^ 2) ≤ Real.sqrt (1 / (n : ℝ) ^ 2) + |x| := by
    have hpos : 0 ≤ Real.sqrt (1 / (n : ℝ) ^ 2) + |x| := by
      have h1 : 0 ≤ Real.sqrt (1 / (n : ℝ) ^ 2) := Real.sqrt_nonneg _
      have h2 : 0 ≤ |x| := abs_nonneg _
      linarith
    have hsq :
        1 / (n : ℝ) ^ 2 + x ^ 2 ≤ (Real.sqrt (1 / (n : ℝ) ^ 2) + |x|) ^ 2 := by
      have hnonneg_term : 0 ≤ 2 * Real.sqrt (1 / (n : ℝ) ^ 2) * |x| := by
        have h1 : 0 ≤ Real.sqrt (1 / (n : ℝ) ^ 2) := Real.sqrt_nonneg _
        have h2 : 0 ≤ |x| := abs_nonneg _
        nlinarith
      have hsq_expand :
          (Real.sqrt (1 / (n : ℝ) ^ 2) + |x|) ^ 2 =
            1 / (n : ℝ) ^ 2 + x ^ 2 + 2 * Real.sqrt (1 / (n : ℝ) ^ 2) * |x| := by
        calc
          (Real.sqrt (1 / (n : ℝ) ^ 2) + |x|) ^ 2 =
              (Real.sqrt (1 / (n : ℝ) ^ 2)) ^ 2 + |x| ^ 2 +
                2 * Real.sqrt (1 / (n : ℝ) ^ 2) * |x| := by
            ring
          _ = 1 / (n : ℝ) ^ 2 + x ^ 2 + 2 * Real.sqrt (1 / (n : ℝ) ^ 2) * |x| := by
            simp [sq_abs]
      calc
        1 / (n : ℝ) ^ 2 + x ^ 2 ≤
            1 / (n : ℝ) ^ 2 + x ^ 2 + 2 * Real.sqrt (1 / (n : ℝ) ^ 2) * |x| := by
          exact le_add_of_nonneg_right hnonneg_term
        _ = (Real.sqrt (1 / (n : ℝ) ^ 2) + |x|) ^ 2 := by
          symm
          exact hsq_expand
    exact (Real.sqrt_le_iff).2 ⟨hpos, hsq⟩
  have hsub :
      Real.sqrt (1 / (n : ℝ) ^ 2 + x ^ 2) - |x| ≤ Real.sqrt (1 / (n : ℝ) ^ 2) := by
    exact (sub_le_iff_le_add).2 hle_sqrt
  have hsqrt : Real.sqrt (1 / (n : ℝ) ^ 2) = (n : ℝ)⁻¹ := by
    have hpow' : 1 / (n : ℝ) ^ 2 = (1 / (n : ℝ)) ^ 2 := by
      symm
      simpa using (one_div_pow (n : ℝ) 2)
    have hnonneg_inv : 0 ≤ (1 / (n : ℝ)) := by
      have hnonneg : 0 ≤ (n : ℝ) := by
        exact_mod_cast (Nat.zero_le n)
      exact (one_div_nonneg).2 hnonneg
    calc
      Real.sqrt (1 / (n : ℝ) ^ 2) = Real.sqrt ((1 / (n : ℝ)) ^ 2) := by
        simp [hpow']
      _ = |1 / (n : ℝ)| := by
        exact Real.sqrt_sq_eq_abs (1 / (n : ℝ))
      _ = (1 / (n : ℝ)) := by
        simp
      _ = (n : ℝ)⁻¹ := by
        simp [one_div]
  calc
    ‖sqrtShiftedSeq n x - absFun x‖ =
        abs (Real.sqrt (1 / (n : ℝ) ^ 2 + x ^ 2) - |x|) := by
      simp [sqrtShiftedSeq, absFun, Real.norm_eq_abs]
    _ = Real.sqrt (1 / (n : ℝ) ^ 2 + x ^ 2) - |x| := by
      exact abs_of_nonneg hnonneg
    _ ≤ Real.sqrt (1 / (n : ℝ) ^ 2) := hsub
    _ = (n : ℝ)⁻¹ := hsqrt

/-- Helper for Proposition 3.20: the inner expression is nonzero for `n ≥ 1`. -/
lemma helperForProposition_3_20_inner_ne_zero_of_one_le (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    (1 / (n : ℝ) ^ 2 + x ^ 2) ≠ 0 := by
  have hnpos_nat : 0 < n := by
    exact lt_of_lt_of_le (Nat.succ_pos 0) hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast hnpos_nat
  have hpowpos : 0 < (n : ℝ) ^ 2 := by
    have hpow : 0 < (n : ℝ) ^ (2 : ℕ) := pow_pos hnpos 2
    simpa using hpow
  have hpos : 0 < 1 / (n : ℝ) ^ 2 := by
    exact one_div_pos.mpr hpowpos
  have hxnonneg : 0 ≤ x ^ 2 := by
    exact sq_nonneg x
  have hsumpos : 0 < 1 / (n : ℝ) ^ 2 + x ^ 2 := by
    exact add_pos_of_pos_of_nonneg hpos hxnonneg
  exact ne_of_gt hsumpos

/-- Helper for Proposition 3.20: differentiability of `sqrtShiftedSeq` for `n ≥ 1`. -/
lemma helperForProposition_3_20_differentiableAt_sqrtShiftedSeq_of_one_le
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    DifferentiableAt ℝ (sqrtShiftedSeq n) x := by
  have hconst :
      DifferentiableAt ℝ (fun _ : ℝ => (1 / (n : ℝ) ^ 2)) x := by
    simpa using
      (differentiableAt_const :
        DifferentiableAt ℝ (fun _ : ℝ => (1 / (n : ℝ) ^ 2)) x)
  have hpow : DifferentiableAt ℝ (fun y : ℝ => y ^ 2) x := by
    simpa using (differentiableAt_pow (𝕜 := ℝ) (𝔸 := ℝ) 2 (x := x))
  have hinner :
      DifferentiableAt ℝ (fun y : ℝ => 1 / (n : ℝ) ^ 2 + y ^ 2) x := by
    simpa using hconst.add hpow
  have hne : (1 / (n : ℝ) ^ 2 + x ^ 2) ≠ 0 :=
    helperForProposition_3_20_inner_ne_zero_of_one_le n hn x
  have hsqrt :
      DifferentiableAt ℝ (fun y : ℝ => Real.sqrt (1 / (n : ℝ) ^ 2 + y ^ 2)) x := by
    exact (DifferentiableAt.sqrt hinner hne)
  change DifferentiableAt ℝ (fun y : ℝ => Real.sqrt (1 / (n : ℝ) ^ 2 + y ^ 2)) x
  exact hsqrt

/-- Helper for Proposition 3.20: differentiability on `[-1,1]` for `n ≥ 1`. -/
lemma helperForProposition_3_20_differentiableOn_sqrtShiftedSeq_of_one_le
    (n : ℕ) (hn : 1 ≤ n) :
    DifferentiableOn ℝ (sqrtShiftedSeq n) (Set.Icc (-1 : ℝ) 1) := by
  intro x hx
  exact
    (helperForProposition_3_20_differentiableAt_sqrtShiftedSeq_of_one_le n hn x).differentiableWithinAt

/-- Helper for Proposition 3.20: differentiability on `[-1,1]` for `n + 1`. -/
lemma helperForProposition_3_20_differentiableOn_sqrtShiftedSeq_succ (n : ℕ) :
    DifferentiableOn ℝ (sqrtShiftedSeq (n + 1)) (Set.Icc (-1 : ℝ) 1) := by
  have hn : 1 ≤ n + 1 := by
    exact Nat.succ_le_succ (Nat.zero_le n)
  exact helperForProposition_3_20_differentiableOn_sqrtShiftedSeq_of_one_le (n + 1) hn

/-- Proposition 3.20: define `f_n(x) = sqrt(1/n^2 + x^2)` and `f(x)=|x|`. Then
`f_n` converges uniformly to `f` on `[-1,1]`, each `f_n` (for `n ≥ 1`) is differentiable on `[-1,1]`,
and `f` is not differentiable at `0`; in particular, a uniform limit of differentiable
functions need not be differentiable. -/
theorem proposition_3_20 :
    TendstoUniformlyOn sqrtShiftedSeq absFun Filter.atTop (Set.Icc (-1 : ℝ) 1) ∧
      (∀ n, 1 ≤ n → DifferentiableOn ℝ (sqrtShiftedSeq n) (Set.Icc (-1 : ℝ) 1)) ∧
        ¬ DifferentiableAt ℝ absFun 0 :=
  by
    refine And.intro ?hUniform ?hRest
    · intro u hu
      rcases Metric.mem_uniformity_dist.1 hu with ⟨ε, hε, hεu⟩
      have hε' :
          ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ)⁻¹ < ε :=
        helperForProposition_3_20_eventually_inv_lt hε
      refine hε'.mono ?_
      intro n hn x hx
      apply hεu
      have hbound :
          ‖sqrtShiftedSeq n x - absFun x‖ ≤ (n : ℝ)⁻¹ :=
        helperForProposition_3_20_norm_sqrtShiftedSeq_sub_absFun_le_inv n x
      have hdist' :
          dist (sqrtShiftedSeq n x) (absFun x) ≤ (n : ℝ)⁻¹ := by
        simpa [dist_eq_norm] using hbound
      have hdist :
          dist (absFun x) (sqrtShiftedSeq n x) ≤ (n : ℝ)⁻¹ := by
        simpa [dist_comm] using hdist'
      exact lt_of_le_of_lt hdist hn
    · refine And.intro ?hDiff ?hNotDiff
      · intro n hn
        exact helperForProposition_3_20_differentiableOn_sqrtShiftedSeq_of_one_le n hn
      · exact helperForProposition_3_20_not_differentiableAt_absFun_zero

/-- Helper for Theorem 3.9: `g` is continuous on `[a,b]` as a uniform limit of continuous
derivatives on `[a,b]`. -/
lemma helperForTheorem_3_9_continuousOn_g_Icc
    {a b : ℝ} (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (h_diff_cont : ∀ n, 1 ≤ n → ContinuousOn (fun x => deriv (f n) x) (Set.Icc a b))
    (h_unif : TendstoUniformlyOn (fun n x => deriv (f n) x) g Filter.atTop (Set.Icc a b)) :
    ContinuousOn g (Set.Icc a b) := by
  have h_cont_eventually :
      ∀ᶠ n : ℕ in Filter.atTop, ContinuousOn (fun x => deriv (f n) x) (Set.Icc a b) :=
    Filter.eventually_atTop.2 ⟨1, fun n hn => h_diff_cont n hn⟩
  exact TendstoUniformlyOn.continuousOn h_unif h_cont_eventually.frequently

/-- Helper for Theorem 3.9: any two points of `[a,b]` are at distance at most `b - a`. -/
lemma helperForTheorem_3_9_abs_sub_le_interval_length
    {a b x x0 : ℝ} (ha : a ≤ b) (hx : x ∈ Set.Icc a b) (hx0 : x0 ∈ Set.Icc a b) :
    |x - x0| ≤ b - a := by
  refine abs_le.2 ?_
  constructor <;> linarith [ha, hx.1, hx.2, hx0.1, hx0.2]

/-- Helper for Theorem 3.9: for `n ≥ 1`, `f_n x - f_n x0` is the integral of `f_n'`
between `x0` and `x`. -/
lemma helperForTheorem_3_9_sub_eq_integral_deriv
    {a b : ℝ} (f : ℕ → ℝ → ℝ)
    (h_diff : ∀ n, 1 ≤ n → DifferentiableOn ℝ (f n) (Set.Icc a b))
    (h_diff_cont : ∀ n, 1 ≤ n → ContinuousOn (fun x => deriv (f n) x) (Set.Icc a b))
    {n : ℕ} (hn : 1 ≤ n) {x0 x : ℝ}
    (hx0 : x0 ∈ Set.Icc a b) (hx : x ∈ Set.Icc a b) :
    f n x - f n x0 = ∫ t in x0..x, deriv (f n) t := by
  have huIcc_subset : Set.uIcc x0 x ⊆ Set.Icc a b :=
    (Set.ordConnected_Icc).uIcc_subset hx0 hx
  have hcont : ContinuousOn (f n) (Set.uIcc x0 x) :=
    (h_diff n hn).continuousOn.mono huIcc_subset
  have hderiv :
      ∀ t ∈ Set.Ioo (min x0 x) (max x0 x),
        HasDerivWithinAt (f n) (deriv (f n) t) (Set.Ioi t) t := by
    intro t ht
    have htuIcc : t ∈ Set.uIcc x0 x := by
      exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have htIcc : t ∈ Set.Icc a b := huIcc_subset htuIcc
    have hamin : a ≤ min x0 x := le_min hx0.1 hx.1
    have hmaxb : max x0 x ≤ b := max_le hx0.2 hx.2
    have hta : a < t := by
      exact lt_of_le_of_lt hamin ht.1
    have htb : t < b := by
      exact lt_of_lt_of_le ht.2 hmaxb
    have hdiffWithin : DifferentiableWithinAt ℝ (f n) (Set.Icc a b) t :=
      h_diff n hn t htIcc
    have hIccNhds : Set.Icc a b ∈ nhds t := Icc_mem_nhds hta htb
    have hderivAt : HasDerivAt (f n) (deriv (f n) t) t :=
      (hdiffWithin.differentiableAt hIccNhds).hasDerivAt
    exact hderivAt.hasDerivWithinAt
  have hint : IntervalIntegrable (fun t => deriv (f n) t) MeasureTheory.volume x0 x :=
    ((h_diff_cont n hn).mono huIcc_subset).intervalIntegrable
  have hIntegral : ∫ t in x0..x, deriv (f n) t = f n x - f n x0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont hderiv hint
  exact hIntegral.symm

/-- Helper for Theorem 3.9: uniform derivative bounds on `[a,b]` control the integral
error term uniformly on `x ∈ [a,b]`. -/
lemma helperForTheorem_3_9_integral_error_bound_on_uIcc
    {a b : ℝ} (ha : a ≤ b) (f : ℕ → ℝ → ℝ) (g gExt : ℝ → ℝ) {n : ℕ}
    {x0 x δ : ℝ}
    (h_gExt_eq : ∀ t ∈ Set.Icc a b, gExt t = g t)
    (h_bound : ∀ t ∈ Set.Icc a b, ‖deriv (f n) t - g t‖ ≤ δ)
    (hδ_nonneg : 0 ≤ δ)
    (hx0 : x0 ∈ Set.Icc a b) (hx : x ∈ Set.Icc a b) :
    ‖∫ t in x0..x, (deriv (f n) t - gExt t)‖ ≤ δ * (b - a) := by
  have huIcc_subset : Set.uIcc x0 x ⊆ Set.Icc a b :=
    (Set.ordConnected_Icc).uIcc_subset hx0 hx
  have hnorm_uIoc : ∀ t ∈ Set.uIoc x0 x, ‖deriv (f n) t - gExt t‖ ≤ δ := by
    intro t ht
    have htIcc : t ∈ Set.Icc a b := huIcc_subset (Set.uIoc_subset_uIcc ht)
    calc
      ‖deriv (f n) t - gExt t‖ = ‖deriv (f n) t - g t‖ := by rw [h_gExt_eq t htIcc]
      _ ≤ δ := h_bound t htIcc
  have h_int : ‖∫ t in x0..x, (deriv (f n) t - gExt t)‖ ≤ δ * |x - x0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hnorm_uIoc
  have h_len : |x - x0| ≤ b - a :=
    helperForTheorem_3_9_abs_sub_le_interval_length ha hx hx0
  have h_mul : δ * |x - x0| ≤ δ * (b - a) :=
    mul_le_mul_of_nonneg_left h_len hδ_nonneg
  exact h_int.trans h_mul

/-- Helper for Theorem 3.9: the distance from `f_n x` to the candidate limit value is bounded by
the basepoint error and an integral error term. -/
lemma helperForTheorem_3_9_dist_bound_fn_to_flim
    {a b : ℝ} (f : ℕ → ℝ → ℝ) (gExt : ℝ → ℝ)
    (h_diff : ∀ n, 1 ≤ n → DifferentiableOn ℝ (f n) (Set.Icc a b))
    (h_diff_cont : ∀ n, 1 ≤ n → ContinuousOn (fun x => deriv (f n) x) (Set.Icc a b))
    {n : ℕ} (hn : 1 ≤ n) {x0 x l : ℝ}
    (hx0 : x0 ∈ Set.Icc a b) (hx : x ∈ Set.Icc a b)
    (h_int_gExt : IntervalIntegrable gExt MeasureTheory.volume x0 x) :
    dist (f n x) (l + ∫ t in x0..x, gExt t) ≤
      dist (f n x0) l + ‖∫ t in x0..x, (deriv (f n) t - gExt t)‖ := by
  have hsub : f n x - f n x0 = ∫ t in x0..x, deriv (f n) t :=
    helperForTheorem_3_9_sub_eq_integral_deriv f h_diff h_diff_cont hn hx0 hx
  have huIcc_subset : Set.uIcc x0 x ⊆ Set.Icc a b :=
    (Set.ordConnected_Icc).uIcc_subset hx0 hx
  have hint_deriv : IntervalIntegrable (fun t => deriv (f n) t) MeasureTheory.volume x0 x :=
    ((h_diff_cont n hn).mono huIcc_subset).intervalIntegrable
  have h_integral_sub :
      (∫ t in x0..x, deriv (f n) t) - (∫ t in x0..x, gExt t) =
        ∫ t in x0..x, (deriv (f n) t - gExt t) := by
    simpa using (intervalIntegral.integral_sub hint_deriv h_int_gExt).symm
  have hrewrite :
      f n x - (l + ∫ t in x0..x, gExt t) =
        (f n x0 - l) + ∫ t in x0..x, (deriv (f n) t - gExt t) := by
    calc
      f n x - (l + ∫ t in x0..x, gExt t)
          = (f n x - f n x0) + (f n x0 - l - ∫ t in x0..x, gExt t) := by ring
      _ = (∫ t in x0..x, deriv (f n) t) + (f n x0 - l - ∫ t in x0..x, gExt t) := by
            rw [hsub]
      _ = (f n x0 - l) + ((∫ t in x0..x, deriv (f n) t) - (∫ t in x0..x, gExt t)) := by ring
      _ = (f n x0 - l) + ∫ t in x0..x, (deriv (f n) t - gExt t) := by rw [h_integral_sub]
  calc
    dist (f n x) (l + ∫ t in x0..x, gExt t)
        = ‖(f n x0 - l) + ∫ t in x0..x, (deriv (f n) t - gExt t)‖ := by
          simpa [dist_eq_norm, hrewrite]
    _ ≤ ‖f n x0 - l‖ + ‖∫ t in x0..x, (deriv (f n) t - gExt t)‖ := norm_add_le _ _
    _ = dist (f n x0) l + ‖∫ t in x0..x, (deriv (f n) t - gExt t)‖ := by
          simp [dist_eq_norm]

/-- Theorem 3.9: if `f_n : [a,b] → ℝ` are differentiable with continuous derivatives,
`f_n'` converges uniformly to `g` on `[a,b]`, and `f_n(x0)` converges for some `x0 ∈ [a,b]`,
then there is a differentiable `f : [a,b] → ℝ` with `f_n → f` uniformly on `[a,b]`
and `f' = g` on `[a,b]`. -/

theorem uniformLimit_of_uniformlyConvergentDerivatives
    {a b : ℝ} (ha : a ≤ b) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (h_diff : ∀ n, 1 ≤ n → DifferentiableOn ℝ (f n) (Set.Icc a b))
    (h_diff_cont : ∀ n, 1 ≤ n → ContinuousOn (fun x => deriv (f n) x) (Set.Icc a b))
    (h_unif : TendstoUniformlyOn (fun n x => deriv (f n) x) g Filter.atTop (Set.Icc a b))
    (hx0 :
      ∃ x0 ∈ Set.Icc a b, ∃ l,
        Filter.Tendsto (fun n => f n x0) Filter.atTop (nhds l)) :
    ∃ f_lim : ℝ → ℝ,
      DifferentiableOn ℝ f_lim (Set.Icc a b) ∧
        TendstoUniformlyOn f f_lim Filter.atTop (Set.Icc a b) ∧
        ∀ x ∈ Set.Icc a b, deriv f_lim x = g x :=
  by
    rcases hx0 with ⟨x0, hx0_mem, l, hx0_tendsto⟩
    have h_cont_g : ContinuousOn g (Set.Icc a b) :=
      helperForTheorem_3_9_continuousOn_g_Icc f g h_diff_cont h_unif
    let gIcc : Set.Icc a b → ℝ := fun x => g x
    have h_gIcc_cont : Continuous gIcc := by
      rw [continuousOn_iff_continuous_restrict] at h_cont_g
      simpa [gIcc] using h_cont_g
    let gExt : ℝ → ℝ := Set.IccExtend ha gIcc
    have h_gExt_cont : Continuous gExt :=
      (continuous_IccExtend_iff (a := a) (b := b) (h := ha) (f := gIcc)).2 h_gIcc_cont
    have h_gExt_eq : ∀ x ∈ Set.Icc a b, gExt x = g x := by
      intro x hx
      simpa [gExt, gIcc] using (Set.IccExtend_of_mem (h := ha) (f := gIcc) hx)
    let f_lim : ℝ → ℝ := fun x => l + ∫ t in x0..x, gExt t
    have h_hasDeriv_f_lim : ∀ x, HasDerivAt f_lim (gExt x) x := by
      intro x
      have hint : IntervalIntegrable gExt MeasureTheory.volume x0 x :=
        h_gExt_cont.intervalIntegrable x0 x
      have hmeas : StronglyMeasurableAtFilter gExt (nhds x) MeasureTheory.volume :=
        Continuous.stronglyMeasurableAtFilter h_gExt_cont MeasureTheory.volume (nhds x)
      have hcontAt : ContinuousAt gExt x := h_gExt_cont.continuousAt
      have hderivInt : HasDerivAt (fun u => ∫ t in x0..u, gExt t) (gExt x) x :=
        intervalIntegral.integral_hasDerivAt_right hint hmeas hcontAt
      have hconst : HasDerivAt (fun _ : ℝ => l) 0 x := hasDerivAt_const x l
      have hsum : HasDerivAt (fun u => l + ∫ t in x0..u, gExt t) (0 + gExt x) x :=
        hconst.add hderivInt
      simpa [f_lim] using hsum
    refine ⟨f_lim, ?_, ?_, ?_⟩
    · intro x hx
      exact (h_hasDeriv_f_lim x).differentiableAt.differentiableWithinAt
    · refine Metric.tendstoUniformlyOn_iff.mpr ?_
      intro ε hε
      let δ : ℝ := ε / (2 * (b - a + 1))
      have hδ_pos : 0 < δ := by
        have hdenom_pos : 0 < 2 * (b - a + 1) := by linarith [ha]
        exact div_pos hε hdenom_pos
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
      have hδ_mul_le_half : δ * (b - a) ≤ ε / 2 := by
        have hstep : δ * (b - a) ≤ δ * (b - a + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hδ_nonneg
          linarith
        have hbap1_ne : b - a + 1 ≠ 0 := by linarith
        have hcalc : δ * (b - a + 1) = ε / 2 := by
          dsimp [δ]
          field_simp [hbap1_ne]
        exact hstep.trans (le_of_eq hcalc)
      have hbase : ∀ᶠ n : ℕ in Filter.atTop, dist (f n x0) l < ε / 2 := by
        have hε_half_pos : 0 < ε / 2 := by linarith
        have hball : Metric.ball l (ε / 2) ∈ nhds l :=
          Metric.ball_mem_nhds l hε_half_pos
        exact Filter.Tendsto.eventually_mem hx0_tendsto hball
      have hderiv_event :
          ∀ᶠ n : ℕ in Filter.atTop, ∀ x ∈ Set.Icc a b, dist (g x) (deriv (f n) x) < δ :=
        (Metric.tendstoUniformlyOn_iff.mp h_unif) δ hδ_pos
      have hone : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ n :=
        Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩
      filter_upwards [hbase, hderiv_event, hone] with n hnBase hnDeriv hnOne x hx
      have h_int_gExt : IntervalIntegrable gExt MeasureTheory.volume x0 x :=
        h_gExt_cont.intervalIntegrable x0 x
      have hdist_bound :
          dist (f n x) (f_lim x) ≤
            dist (f n x0) l + ‖∫ t in x0..x, (deriv (f n) t - gExt t)‖ := by
        simpa [f_lim] using
          (helperForTheorem_3_9_dist_bound_fn_to_flim f gExt h_diff h_diff_cont hnOne
            hx0_mem hx h_int_gExt)
      have hderiv_norm_le : ∀ t ∈ Set.Icc a b, ‖deriv (f n) t - g t‖ ≤ δ := by
        intro t ht
        have hlt : dist (g t) (deriv (f n) t) < δ := hnDeriv t ht
        have hlt' : dist (deriv (f n) t) (g t) < δ := by simpa [dist_comm] using hlt
        exact le_of_lt (by simpa [dist_eq_norm] using hlt')
      have hIntLe :
          ‖∫ t in x0..x, (deriv (f n) t - gExt t)‖ ≤ δ * (b - a) :=
        helperForTheorem_3_9_integral_error_bound_on_uIcc ha f g gExt h_gExt_eq
          hderiv_norm_le hδ_nonneg hx0_mem hx
      have hIntHalf : ‖∫ t in x0..x, (deriv (f n) t - gExt t)‖ ≤ ε / 2 :=
        hIntLe.trans hδ_mul_le_half
      have hsum : dist (f n x) (f_lim x) < ε := by
        have hsum_half : dist (f n x) (f_lim x) < ε / 2 + ε / 2 :=
          lt_of_le_of_lt hdist_bound (add_lt_add_of_lt_of_le hnBase hIntHalf)
        have hhalf : ε / 2 + ε / 2 = ε := by ring
        exact hhalf ▸ hsum_half
      simpa [dist_comm] using hsum
    · intro x hx
      have hderiv_eq : deriv f_lim x = gExt x := (h_hasDeriv_f_lim x).deriv
      rw [hderiv_eq, h_gExt_eq x hx]

/-- The sup norm of a function on a set, defined as the supremum of `‖f x‖` over the set. -/
noncomputable def supNormOn {α β : Type*} [NormedAddCommGroup β] (s : Set α) (f : α → β) : ℝ :=
  sSup ((fun x => ‖f x‖) '' s)

/-- Helper for Theorem 3.10: a pointwise derivative norm on `[a,b]` is bounded by the
corresponding sup norm. -/
lemma helperForTheorem_3_10_norm_deriv_le_supNormOn
    {a b : ℝ} (f : ℕ → ℝ → ℝ)
    (h_diff_cont :
      ∀ n : ℕ, ContinuousOn (fun x => deriv (f (n + 1)) x) (Set.Icc a b))
    (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ‖deriv (f (n + 1)) x‖ ≤
      supNormOn (Set.Icc a b) (fun y => deriv (f (n + 1)) y) := by
  have hcont_norm :
      ContinuousOn (fun y => ‖deriv (f (n + 1)) y‖) (Set.Icc a b) :=
    (h_diff_cont n).norm
  have hbdd :
      BddAbove ((fun y => ‖deriv (f (n + 1)) y‖) '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hcont_norm).bddAbove
  have hmem :
      ‖deriv (f (n + 1)) x‖ ∈ ((fun y => ‖deriv (f (n + 1)) y‖) '' Set.Icc a b) :=
    Set.mem_image_of_mem (fun y => ‖deriv (f (n + 1)) y‖) hx
  simpa [supNormOn] using (le_csSup hbdd hmem)

/-- Helper for Theorem 3.10: derivative partial sums converge uniformly on `[a,b]` to the
termwise derivative series. -/
lemma helperForTheorem_3_10_tendstoUniformlyOn_derivSeries
    {a b : ℝ} (f : ℕ → ℝ → ℝ)
    (h_diff_cont :
      ∀ n : ℕ, ContinuousOn (fun x => deriv (f (n + 1)) x) (Set.Icc a b))
    (h_summable :
      Summable
        (fun n : ℕ =>
          supNormOn (Set.Icc a b) (fun x => deriv (f (n + 1)) x))) :
    TendstoUniformlyOn
      (fun N x => (Finset.range N).sum (fun n => deriv (f (n + 1)) x))
      (fun x => tsum (fun n : ℕ => deriv (f (n + 1)) x))
      Filter.atTop (Set.Icc a b) := by
  refine tendstoUniformlyOn_tsum_nat h_summable ?_
  intro n x hx
  simpa using helperForTheorem_3_10_norm_deriv_le_supNormOn f h_diff_cont n hx

/-- Helper for Theorem 3.10: lifted partial sums based at `x0`, built from an integral of the
`IccExtend` of derivative partial sums. -/
noncomputable def helperForTheorem_3_10_liftedPartialSum
    {a b : ℝ} (ha : a ≤ b) (f : ℕ → ℝ → ℝ) (x0 : ℝ) (N : ℕ) : ℝ → ℝ :=
  fun x =>
    (Finset.range N).sum (fun n => f (n + 1) x0) +
      ∫ t in x0..x,
        Set.IccExtend ha
          (fun y : Set.Icc a b =>
            (Finset.range N).sum (fun n => deriv (f (n + 1)) y)) t

/-- Helper for Theorem 3.10: continuity of the subtype derivative partial-sum map. -/
lemma helperForTheorem_3_10_continuous_subtype_derivPartialSum
    {a b : ℝ} (f : ℕ → ℝ → ℝ)
    (h_diff_cont :
      ∀ n : ℕ, ContinuousOn (fun x => deriv (f (n + 1)) x) (Set.Icc a b))
    (N : ℕ) :
    Continuous
      (fun y : Set.Icc a b =>
        (Finset.range N).sum (fun n => deriv (f (n + 1)) y)) := by
  induction N with
  | zero =>
      simpa using (continuous_const : Continuous (fun _ : Set.Icc a b => (0 : ℝ)))
  | succ N ih =>
      have hterm : Continuous (fun y : Set.Icc a b => deriv (f (N + 1)) y) := by
        have hcont : ContinuousOn (fun x => deriv (f (N + 1)) x) (Set.Icc a b) := h_diff_cont N
        rw [continuousOn_iff_continuous_restrict] at hcont
        simpa using hcont
      simpa [Finset.sum_range_succ] using ih.add hterm

/-- Helper for Theorem 3.10: the lifted partial sum has derivative equal to the corresponding
`IccExtend` derivative partial sum. -/
lemma helperForTheorem_3_10_hasDerivAt_liftedPartialSum
    {a b : ℝ} (ha : a ≤ b) (f : ℕ → ℝ → ℝ)
    (h_diff_cont :
      ∀ n : ℕ, ContinuousOn (fun x => deriv (f (n + 1)) x) (Set.Icc a b))
    (x0 : ℝ) (N : ℕ) (x : ℝ) :
    HasDerivAt
      (helperForTheorem_3_10_liftedPartialSum ha f x0 N)
      (Set.IccExtend ha
        (fun y : Set.Icc a b =>
          (Finset.range N).sum (fun n => deriv (f (n + 1)) y)) x)
      x := by
  let gN : ℝ → ℝ :=
    Set.IccExtend ha
      (fun y : Set.Icc a b =>
        (Finset.range N).sum (fun n => deriv (f (n + 1)) y))
  have h_subtype_cont :
      Continuous
        (fun y : Set.Icc a b =>
          (Finset.range N).sum (fun n => deriv (f (n + 1)) y)) :=
    helperForTheorem_3_10_continuous_subtype_derivPartialSum f h_diff_cont N
  have h_gN_cont : Continuous gN :=
    (continuous_IccExtend_iff (a := a) (b := b) (h := ha)
      (f :=
        fun y : Set.Icc a b =>
          (Finset.range N).sum (fun n => deriv (f (n + 1)) y))).2 h_subtype_cont
  have hint : IntervalIntegrable gN MeasureTheory.volume x0 x :=
    h_gN_cont.intervalIntegrable x0 x
  have hmeas : StronglyMeasurableAtFilter gN (nhds x) MeasureTheory.volume :=
    Continuous.stronglyMeasurableAtFilter h_gN_cont MeasureTheory.volume (nhds x)
  have hcontAt : ContinuousAt gN x := h_gN_cont.continuousAt
  have hderivInt : HasDerivAt (fun u => ∫ t in x0..u, gN t) (gN x) x :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hcontAt
  have hsum :
      HasDerivAt
        (fun u =>
          (Finset.range N).sum (fun n => f (n + 1) x0) +
            ∫ t in x0..u, gN t)
        (gN x) x :=
    (hderivInt.const_add ((Finset.range N).sum (fun n => f (n + 1) x0)))
  change HasDerivAt
    (fun u =>
      (Finset.range N).sum (fun n => f (n + 1) x0) +
        ∫ t in x0..u,
          Set.IccExtend ha
            (fun y : Set.Icc a b =>
              (Finset.range N).sum (fun n => deriv (f (n + 1)) y)) t)
    (gN x) x
  simpa [gN] using hsum

/-- Helper for Theorem 3.10: explicit formula for the derivative of a lifted partial sum. -/
lemma helperForTheorem_3_10_deriv_liftedPartialSum
    {a b : ℝ} (ha : a ≤ b) (f : ℕ → ℝ → ℝ)
    (h_diff_cont :
      ∀ n : ℕ, ContinuousOn (fun x => deriv (f (n + 1)) x) (Set.Icc a b))
    (x0 : ℝ) (N : ℕ) (x : ℝ) :
    deriv (helperForTheorem_3_10_liftedPartialSum ha f x0 N) x =
      Set.IccExtend ha
        (fun y : Set.Icc a b =>
          (Finset.range N).sum (fun n => deriv (f (n + 1)) y)) x :=
  (helperForTheorem_3_10_hasDerivAt_liftedPartialSum ha f h_diff_cont x0 N x).deriv

/-- Helper for Theorem 3.10: on `[a,b]`, the derivative of the lifted partial sum equals the
raw derivative partial sum. -/
lemma helperForTheorem_3_10_deriv_liftedPartialSum_on_Icc
    {a b : ℝ} (ha : a ≤ b) (f : ℕ → ℝ → ℝ)
    (h_diff_cont :
      ∀ n : ℕ, ContinuousOn (fun x => deriv (f (n + 1)) x) (Set.Icc a b))
    (x0 : ℝ) (N : ℕ) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    deriv (helperForTheorem_3_10_liftedPartialSum ha f x0 N) x =
      (Finset.range N).sum (fun n => deriv (f (n + 1)) x) := by
  rw [helperForTheorem_3_10_deriv_liftedPartialSum ha f h_diff_cont x0 N x]
  simpa using
    (Set.IccExtend_of_mem (h := ha)
      (f :=
        fun y : Set.Icc a b =>
          (Finset.range N).sum (fun n => deriv (f (n + 1)) y)) hx)

/-- Helper for Theorem 3.10: each lifted partial sum is differentiable on `[a,b]`. -/
lemma helperForTheorem_3_10_differentiableOn_liftedPartialSum
    {a b : ℝ} (ha : a ≤ b) (f : ℕ → ℝ → ℝ)
    (h_diff_cont :
      ∀ n : ℕ, ContinuousOn (fun x => deriv (f (n + 1)) x) (Set.Icc a b))
    (x0 : ℝ) (N : ℕ) :
    DifferentiableOn ℝ (helperForTheorem_3_10_liftedPartialSum ha f x0 N) (Set.Icc a b) := by
  intro x hx
  have hderivAt :
      HasDerivAt
        (helperForTheorem_3_10_liftedPartialSum ha f x0 N)
        (Set.IccExtend ha
          (fun y : Set.Icc a b =>
            (Finset.range N).sum (fun n => deriv (f (n + 1)) y)) x)
        x :=
    helperForTheorem_3_10_hasDerivAt_liftedPartialSum ha f h_diff_cont x0 N x
  exact hderivAt.differentiableAt.differentiableWithinAt

/-- Helper for Theorem 3.10: the derivative of each lifted partial sum is continuous on
`[a,b]`. -/
lemma helperForTheorem_3_10_continuousOn_deriv_liftedPartialSum
    {a b : ℝ} (ha : a ≤ b) (f : ℕ → ℝ → ℝ)
    (h_diff_cont :
      ∀ n : ℕ, ContinuousOn (fun x => deriv (f (n + 1)) x) (Set.Icc a b))
    (x0 : ℝ) (N : ℕ) :
    ContinuousOn
      (fun x => deriv (helperForTheorem_3_10_liftedPartialSum ha f x0 N) x)
      (Set.Icc a b) := by
  let gN : ℝ → ℝ :=
    Set.IccExtend ha
      (fun y : Set.Icc a b =>
        (Finset.range N).sum (fun n => deriv (f (n + 1)) y))
  have h_subtype_cont :
      Continuous
        (fun y : Set.Icc a b =>
          (Finset.range N).sum (fun n => deriv (f (n + 1)) y)) :=
    helperForTheorem_3_10_continuous_subtype_derivPartialSum f h_diff_cont N
  have h_gN_cont : Continuous gN :=
    (continuous_IccExtend_iff (a := a) (b := b) (h := ha)
      (f :=
        fun y : Set.Icc a b =>
          (Finset.range N).sum (fun n => deriv (f (n + 1)) y))).2 h_subtype_cont
  have hderiv_eq :
      (fun x => deriv (helperForTheorem_3_10_liftedPartialSum ha f x0 N) x) = gN := by
    funext x
    simpa [gN] using helperForTheorem_3_10_deriv_liftedPartialSum ha f h_diff_cont x0 N x
  rw [hderiv_eq]
  exact h_gN_cont.continuousOn

/-- Helper for Theorem 3.10: on `[a,b]`, each lifted partial sum coincides with the corresponding
raw partial sum of `f`. -/
lemma helperForTheorem_3_10_lifted_eq_rawPartialSum_on_Icc
    {a b : ℝ} (ha : a ≤ b) (f : ℕ → ℝ → ℝ)
    (h_diff : ∀ n : ℕ, DifferentiableOn ℝ (f (n + 1)) (Set.Icc a b))
    (h_diff_cont :
      ∀ n : ℕ, ContinuousOn (fun x => deriv (f (n + 1)) x) (Set.Icc a b))
    {x0 x : ℝ} (hx0 : x0 ∈ Set.Icc a b) (hx : x ∈ Set.Icc a b) (N : ℕ) :
    helperForTheorem_3_10_liftedPartialSum ha f x0 N x =
      (Finset.range N).sum (fun n => f (n + 1) x) := by
  have h_diff_shift :
      ∀ m, 1 ≤ m → DifferentiableOn ℝ (f m) (Set.Icc a b) := by
    intro m hm
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
    rw [hk]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_diff k
  have h_diff_cont_shift :
      ∀ m, 1 ≤ m → ContinuousOn (fun y => deriv (f m) y) (Set.Icc a b) := by
    intro m hm
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
    rw [hk]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_diff_cont k
  have huIcc_subset : Set.uIcc x0 x ⊆ Set.Icc a b :=
    (Set.ordConnected_Icc).uIcc_subset hx0 hx
  have hInt_eq :
      ∫ t in x0..x,
        Set.IccExtend ha
          (fun y : Set.Icc a b =>
            (Finset.range N).sum (fun n => deriv (f (n + 1)) y)) t =
      ∫ t in x0..x, (Finset.range N).sum (fun n => deriv (f (n + 1)) t) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have htIcc : t ∈ Set.Icc a b := huIcc_subset ht
    simpa using
      (Set.IccExtend_of_mem (h := ha)
        (f :=
          fun y : Set.Icc a b =>
            (Finset.range N).sum (fun n => deriv (f (n + 1)) y)) htIcc)
  have hInt_sum :
      ∫ t in x0..x, (Finset.range N).sum (fun n => deriv (f (n + 1)) t) =
        (Finset.range N).sum (fun n => (f (n + 1) x - f (n + 1) x0)) := by
    calc
      ∫ t in x0..x, (Finset.range N).sum (fun n => deriv (f (n + 1)) t)
          = (Finset.range N).sum (fun n => ∫ t in x0..x, deriv (f (n + 1)) t) := by
              refine intervalIntegral.integral_finset_sum (μ := MeasureTheory.volume)
                (f := fun n t => (deriv (f (n + 1)) t : ℝ)) ?_
              intro n hn
              exact ((h_diff_cont n).mono huIcc_subset).intervalIntegrable
      _ = (Finset.range N).sum (fun n => (f (n + 1) x - f (n + 1) x0)) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            have hn1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
            simpa using
              (helperForTheorem_3_9_sub_eq_integral_deriv
                (a := a) (b := b) (f := f)
                h_diff_shift h_diff_cont_shift (n := n + 1) hn1 hx0 hx).symm
  have hsum_eq :
      (Finset.range N).sum (fun n => f (n + 1) x0) +
          (Finset.range N).sum (fun n => (f (n + 1) x - f (n + 1) x0)) =
        (Finset.range N).sum (fun n => f (n + 1) x) := by
    calc
      (Finset.range N).sum (fun n => f (n + 1) x0) +
          (Finset.range N).sum (fun n => (f (n + 1) x - f (n + 1) x0))
          = (Finset.range N).sum
              (fun n => f (n + 1) x0 + (f (n + 1) x - f (n + 1) x0)) := by
                rw [← Finset.sum_add_distrib]
      _ = (Finset.range N).sum (fun n => f (n + 1) x) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            ring
  calc
    helperForTheorem_3_10_liftedPartialSum ha f x0 N x
        = (Finset.range N).sum (fun n => f (n + 1) x0) +
            ∫ t in x0..x,
              Set.IccExtend ha
                (fun y : Set.Icc a b =>
                  (Finset.range N).sum (fun n => deriv (f (n + 1)) y)) t := by
              rfl
    _ = (Finset.range N).sum (fun n => f (n + 1) x0) +
          ∫ t in x0..x, (Finset.range N).sum (fun n => deriv (f (n + 1)) t) := by
            rw [hInt_eq]
    _ = (Finset.range N).sum (fun n => f (n + 1) x0) +
          (Finset.range N).sum (fun n => (f (n + 1) x - f (n + 1) x0)) := by
            rw [hInt_sum]
    _ = (Finset.range N).sum (fun n => f (n + 1) x) := hsum_eq


end Section07
end Chap03
