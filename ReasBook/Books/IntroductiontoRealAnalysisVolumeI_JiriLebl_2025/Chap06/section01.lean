/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import Mathlib

section Chap06
section Section01

universe u

open Filter
open scoped Topology
open scoped BigOperators

/-- Definition 6.1.1: A sequence of functions `fₙ : S → ℝ` converges pointwise
to `f : S → ℝ` if for every `x ∈ S`, the real sequence `fₙ x` converges to
`f x` (this is the default meaning of "converges" for sequences of functions
unless specified otherwise). -/
def pointwiseConverges {S : Type u} (f : ℕ → S → ℝ) (g : S → ℝ) : Prop :=
  ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))

/-- Proposition 6.1.5: A sequence of functions `fₙ : S → ℝ` converges
pointwise to `f : S → ℝ` if and only if for every `x ∈ S` and every `ε > 0`
there exists `N` such that `|fₙ x - f x| < ε` for all `n ≥ N`. -/
theorem pointwiseConverges_iff_abs_sub_lt {S : Type u} (f : ℕ → S → ℝ)
    (g : S → ℝ) :
    pointwiseConverges f g ↔
      ∀ x : S, ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, |f n x - g x| < ε := by
  unfold pointwiseConverges
  constructor
  · intro h x ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (h x) ε hε
    refine ⟨N, ?_⟩
    intro n hn
    simpa [Real.dist_eq] using hN n hn
  · intro h x
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    obtain ⟨N, hN⟩ := h x ε hε
    refine ⟨N, ?_⟩
    intro n hn
    simpa [Real.dist_eq] using hN n hn

/-- Example 6.1.2: On `[-1,1]`, the sequence `fₙ x := x^(2 n)` converges
pointwise to the function that is `1` at `x = -1` and `x = 1`, and `0`
everywhere else in the closed interval. Outside `[-1,1]` the powers
`x^(2 n)` do not converge. -/
lemma pointwiseConverges_pow_even :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      Tendsto (fun n : ℕ => x ^ (2 * n)) atTop
        (𝓝 (if x = 1 ∨ x = -1 then (1 : ℝ) else 0)) := by
  intro x hx
  by_cases h : x = 1 ∨ x = -1
  · have hconst : (fun n : ℕ => x ^ (2 * n)) = fun _ => (1 : ℝ) := by
      funext n
      rcases h with h1 | h2
      · simp [h1]
      · simp [h2, pow_mul]
    simp [h, hconst]
  · have hx_ne1 : x ≠ 1 := by
      intro h1
      exact h (Or.inl h1)
    have hx_ne_neg1 : x ≠ -1 := by
      intro h2
      exact h (Or.inr h2)
    have hx_lt1 : x < 1 := lt_of_le_of_ne hx.2 hx_ne1
    have hx_ne_neg1' : (-1 : ℝ) ≠ x := by
      intro h'
      apply hx_ne_neg1
      simpa [eq_comm] using h'
    have hx_gt_neg1 : -1 < x := lt_of_le_of_ne hx.1 hx_ne_neg1'
    have hx_abs : |x| < 1 := (abs_lt).2 ⟨hx_gt_neg1, hx_lt1⟩
    have hx2_nonneg : 0 ≤ x ^ 2 := by
      simpa [pow_two] using sq_nonneg x
    have hx2_lt1 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).2 hx_abs
    have hpow : Tendsto (fun n : ℕ => (x ^ 2) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hx2_nonneg hx2_lt1
    have hpow' : Tendsto (fun n : ℕ => x ^ (2 * n)) atTop (𝓝 0) := by
      simpa [pow_mul] using hpow
    simpa [h] using hpow'

/-- Example 6.1.3: For `x ∈ (-1, 1)` the partial sums of the geometric series
`fₙ(x) = \sum_{k=0}^n x^k` converge to `1 / (1 - x)`, so the function
`\sum_{k=0}^\infty x^k` is defined on `(-1, 1)` as this limit. -/
lemma tendsto_partialSums_geometric_of_abs_lt_one :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      Tendsto (fun n : ℕ =>
        Finset.sum (Finset.range (n + 1)) (fun k => x ^ k)) atTop
        (𝓝 (1 / (1 - x))) := by
  intro x hx
  have hx_abs : |x| < 1 := (abs_lt).2 ⟨hx.1, hx.2⟩
  have hx_norm : ‖x‖ < 1 := by
    simpa [Real.norm_eq_abs] using hx_abs
  have hsum : HasSum (fun n : ℕ => x ^ n) (1 - x)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hx_norm
  have hlim :
      Tendsto (fun n : ℕ => Finset.sum (Finset.range n) (fun k => x ^ k)) atTop
        (𝓝 (1 - x)⁻¹) :=
    hsum.tendsto_sum_nat
  have hlim' :
      Tendsto (fun n : ℕ =>
        Finset.sum (Finset.range (n + 1)) (fun k => x ^ k)) atTop
        (𝓝 (1 - x)⁻¹) := by
    simpa using
      (tendsto_add_atTop_iff_nat
        (f := fun n : ℕ => Finset.sum (Finset.range n) (fun k => x ^ k))
        (k := 1)).2 hlim
  simpa [one_div] using hlim'

/-- Example 6.1.4: The sequence of functions `fₙ(x) = \sin (n x)` does not
converge pointwise to any function on any interval, even though it converges
at isolated points such as `x = 0` or `x = π`. -/
lemma tendsto_sin_nat_mul_zero :
    Tendsto (fun n : ℕ => Real.sin ((n : ℝ) * 0)) atTop (𝓝 0) := by
  simp [mul_zero]

/-- A concrete convergent point for `fₙ(x) = \sin (n x)` is `x = π`, where
the sequence is constantly zero. -/
lemma tendsto_sin_nat_mul_pi :
    Tendsto (fun n : ℕ => Real.sin ((n : ℝ) * Real.pi)) atTop (𝓝 0) := by
  have h : (fun n : ℕ => Real.sin ((n : ℝ) * Real.pi)) = fun _ => (0 : ℝ) := by
    funext n
    simpa [mul_comm] using Real.sin_nat_mul_pi n
  simp

/-- In any nontrivial interval, we can choose `x` with `x / (2π)` irrational. -/
lemma exists_irrational_div_two_pi_in_Icc {a b : ℝ} (h : a < b) :
    ∃ x ∈ Set.Icc a b, Irrational (x / (2 * Real.pi)) := by
  have hpi : 0 < (2 * Real.pi) := by
    have hpi' : 0 < Real.pi := Real.pi_pos
    linarith
  have hlt : a / (2 * Real.pi) < b / (2 * Real.pi) := by
    exact (div_lt_div_iff_of_pos_right hpi).2 h
  obtain ⟨y, hy_irr, hy_lt, hy_gt⟩ := exists_irrational_btwn hlt
  refine ⟨y * (2 * Real.pi), ?_, ?_⟩
  · have hy_lt' : a < y * (2 * Real.pi) := (div_lt_iff₀ hpi).1 hy_lt
    have hy_gt' : y * (2 * Real.pi) < b := (lt_div_iff₀ hpi).1 hy_gt
    exact ⟨le_of_lt hy_lt', le_of_lt hy_gt'⟩
  · have hne : (2 * Real.pi : ℝ) ≠ 0 := by nlinarith [hpi]
    simpa [hne] using hy_irr

lemma not_tendsto_sin_nat_mul_of_irrational {x : ℝ}
    (hx : Irrational (x / (2 * Real.pi))) :
    ¬ ∃ l : ℝ, Tendsto (fun n : ℕ => Real.sin ((n : ℝ) * x)) atTop (𝓝 l) := by
  intro h
  rcases h with ⟨l, hsin⟩
  have hsin_shift :
      Tendsto (fun n : ℕ => Real.sin (((n + 1 : ℕ) : ℝ) * x)) atTop (𝓝 l) := by
    simpa using
      (tendsto_add_atTop_iff_nat (f := fun n : ℕ => Real.sin ((n : ℝ) * x)) (k := 1)).2 hsin
  by_cases hsinx : Real.sin x = 0
  · rcases Real.sin_eq_zero_iff.1 hsinx with ⟨n, hn⟩
    have hpi : (Real.pi : ℝ) ≠ 0 := by nlinarith [Real.pi_pos]
    have hxrat : x / (2 * Real.pi) ∈ Set.range ((↑) : ℚ → ℝ) := by
      refine ⟨(n : ℚ) / 2, ?_⟩
      have hx : x / (2 * Real.pi) = (n : ℝ) / 2 := by
        calc
          x / (2 * Real.pi) = ((n : ℝ) * Real.pi) / (2 * Real.pi) := by simp [hn]
          _ = (n : ℝ) / 2 := by
            simpa [mul_comm] using
              (mul_div_mul_left (a := (n : ℝ)) (b := (2 : ℝ)) (c := Real.pi) hpi)
      simp [hx]
    exact hx hxrat
  · set c : ℝ := (l - l * Real.cos x) / Real.sin x with hc
    have hsin_add :
        (fun n : ℕ => Real.sin ((↑n + 1) * x)) =
          fun n : ℕ => Real.sin ((n : ℝ) * x) * Real.cos x +
            Real.cos ((n : ℝ) * x) * Real.sin x := by
      funext n
      simp [add_mul, Real.sin_add]
    have hsin_shift' :
        Tendsto (fun n : ℕ => Real.sin ((n : ℝ) * x) * Real.cos x +
          Real.cos ((n : ℝ) * x) * Real.sin x) atTop (𝓝 l) := by
      simpa [hsin_add] using hsin_shift
    have hA :
        Tendsto (fun n : ℕ => Real.sin ((n : ℝ) * x) * Real.cos x) atTop
          (𝓝 (l * Real.cos x)) :=
      hsin.mul_const (Real.cos x)
    have hcos_term :
        Tendsto (fun n : ℕ => Real.cos ((n : ℝ) * x) * Real.sin x) atTop
          (𝓝 (l - l * Real.cos x)) := by
      have hdiff := hsin_shift'.sub hA
      simpa [add_sub_cancel_left] using hdiff
    have hcos : Tendsto (fun n : ℕ => Real.cos ((n : ℝ) * x)) atTop (𝓝 c) := by
      have hmul := hcos_term.mul_const (1 / Real.sin x)
      simpa [hc, div_eq_mul_inv, mul_assoc, hsinx] using hmul
    have hcos_add :
        (fun n : ℕ => Real.cos ((↑n + 1) * x)) =
          fun n : ℕ => Real.cos ((n : ℝ) * x) * Real.cos x -
            Real.sin ((n : ℝ) * x) * Real.sin x := by
      funext n
      simp [add_mul, Real.cos_add]
    have hcos_shift : Tendsto (fun n : ℕ => Real.cos (((n + 1 : ℕ) : ℝ) * x)) atTop (𝓝 c) := by
      simpa using
        (tendsto_add_atTop_iff_nat (f := fun n : ℕ => Real.cos ((n : ℝ) * x)) (k := 1)).2 hcos
    have hcos_shift' :
        Tendsto (fun n : ℕ => Real.cos ((n : ℝ) * x) * Real.cos x -
          Real.sin ((n : ℝ) * x) * Real.sin x) atTop (𝓝 c) := by
      simpa [hcos_add] using hcos_shift
    have hcos_sum :
        Tendsto (fun n : ℕ => Real.cos ((n : ℝ) * x) * Real.cos x -
          Real.sin ((n : ℝ) * x) * Real.sin x) atTop
          (𝓝 (c * Real.cos x - l * Real.sin x)) := by
      have hA' :
          Tendsto (fun n : ℕ => Real.cos ((n : ℝ) * x) * Real.cos x) atTop
            (𝓝 (c * Real.cos x)) :=
        hcos.mul_const (Real.cos x)
      have hB' :
          Tendsto (fun n : ℕ => Real.sin ((n : ℝ) * x) * Real.sin x) atTop
            (𝓝 (l * Real.sin x)) :=
        hsin.mul_const (Real.sin x)
      exact hA'.sub hB'
    have hcos_eq : c = c * Real.cos x - l * Real.sin x :=
      tendsto_nhds_unique hcos_shift' hcos_sum
    have hsin_sum :
        Tendsto (fun n : ℕ => Real.sin ((n : ℝ) * x) * Real.cos x +
          Real.cos ((n : ℝ) * x) * Real.sin x) atTop
          (𝓝 (l * Real.cos x + c * Real.sin x)) := by
      have hA1 :
          Tendsto (fun n : ℕ => Real.sin ((n : ℝ) * x) * Real.cos x) atTop
            (𝓝 (l * Real.cos x)) :=
        hsin.mul_const (Real.cos x)
      have hB1 :
          Tendsto (fun n : ℕ => Real.cos ((n : ℝ) * x) * Real.sin x) atTop
            (𝓝 (c * Real.sin x)) :=
        hcos.mul_const (Real.sin x)
      exact hA1.add hB1
    have hsin_eq : l = l * Real.cos x + c * Real.sin x :=
      tendsto_nhds_unique hsin_shift' hsin_sum
    have hsin_sq :
        Tendsto (fun n : ℕ => Real.sin ((n : ℝ) * x) ^ 2) atTop (𝓝 (l ^ 2)) :=
      hsin.pow 2
    have hcos_sq :
        Tendsto (fun n : ℕ => Real.cos ((n : ℝ) * x) ^ 2) atTop (𝓝 (c ^ 2)) :=
      hcos.pow 2
    have hsum_sq :
        Tendsto (fun n : ℕ => Real.sin ((n : ℝ) * x) ^ 2 +
          Real.cos ((n : ℝ) * x) ^ 2) atTop (𝓝 (l ^ 2 + c ^ 2)) :=
      hsin_sq.add hcos_sq
    have hsum_const :
        Tendsto (fun n : ℕ => Real.sin ((n : ℝ) * x) ^ 2 +
          Real.cos ((n : ℝ) * x) ^ 2) atTop (𝓝 (1 : ℝ)) := by
      simp
    have hsum : l ^ 2 + c ^ 2 = 1 :=
      tendsto_nhds_unique hsum_sq hsum_const
    have hAeq : (1 - Real.cos x) * l = c * Real.sin x := by linarith [hsin_eq]
    have hBeq : (1 - Real.cos x) * c = - l * Real.sin x := by linarith [hcos_eq]
    have hEq : c ^ 2 * Real.sin x = - l ^ 2 * Real.sin x := by
      calc
        c ^ 2 * Real.sin x = c * (c * Real.sin x) := by
          simp [pow_two, mul_assoc]
        _ = c * ((1 - Real.cos x) * l) := by
          simp [hAeq.symm]
        _ = l * ((1 - Real.cos x) * c) := by
          ring
        _ = l * (- l * Real.sin x) := by
          simp [hBeq]
        _ = - l ^ 2 * Real.sin x := by
          simp [pow_two, mul_assoc]
    have hmul : (c ^ 2 + l ^ 2) * Real.sin x = 0 := by
      have htmp : c ^ 2 * Real.sin x + l ^ 2 * Real.sin x = 0 := by
        linarith [hEq]
      simpa [mul_add, add_mul, mul_assoc] using htmp
    have hsum_zero : c ^ 2 + l ^ 2 = 0 := by
      rcases mul_eq_zero.mp hmul with hzero | hzero
      · exact hzero
      · exact (hsinx hzero).elim
    have hsum' : c ^ 2 + l ^ 2 = 1 := by
      simpa [add_comm] using hsum
    linarith [hsum', hsum_zero]

/-- For any interval `[a, b]` there is a point where the sequence
`fₙ(x) = \sin (n x)` fails to converge. -/
theorem exists_nonconvergent_sin_nat_mul (a b : ℝ) (h : a < b) :
    ∃ x ∈ Set.Icc a b,
      ¬ ∃ l : ℝ, Tendsto (fun n : ℕ => Real.sin ((n : ℝ) * x)) atTop (𝓝 l) := by
  obtain ⟨x, hx, hirr⟩ := exists_irrational_div_two_pi_in_Icc (a := a) (b := b) h
  exact ⟨x, hx, not_tendsto_sin_nat_mul_of_irrational hirr⟩

/-- Definition 6.1.6: A sequence of functions `fₙ : S → ℝ` converges uniformly
to `f : S → ℝ` if for every `ε > 0` there exists `N` such that for all `n ≥ N`
and all `x ∈ S`, we have `|fₙ x - f x| < ε`. -/
def uniformConverges {S : Type u} (f : ℕ → S → ℝ) (g : S → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ x : S, |f n x - g x| < ε

/-- Proposition 6.1.7: If a sequence of functions `fₙ : S → ℝ` converges
uniformly to `f : S → ℝ`, then it converges pointwise to `f`. -/
theorem uniformConverges.pointwiseConverges {S : Type u} (f : ℕ → S → ℝ)
    (g : S → ℝ) (h : uniformConverges f g) : pointwiseConverges f g := by
  refine (pointwiseConverges_iff_abs_sub_lt f g).2 ?_
  intro x ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, ?_⟩
  intro n hn
  exact hN n hn x

/-- Helper for Example 6.1.8: for any `N` there is `x ∈ (-1,1)` with
`x^(2N) > 1/2`. -/
lemma exists_x_pow_even_ge_half (N : ℕ) :
    ∃ x ∈ Set.Ioo (-1 : ℝ) 1, x ^ (2 * N) > (1 / 2 : ℝ) := by
  let x : ℕ → ℝ := fun k => 1 - 1 / ((k : ℝ) + 1)
  have hx_tendsto : Tendsto x atTop (𝓝 (1 : ℝ)) := by
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds
    have h2 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have h := h1.sub h2
    simpa [x] using h
  have hxpow_tendsto :
      Tendsto (fun k : ℕ => (x k) ^ (2 * N)) atTop (𝓝 (1 : ℝ)) := by
    have hcont : Continuous (fun t : ℝ => t ^ (2 * N)) := by
      simpa using (continuous_pow (n := 2 * N) : Continuous fun t : ℝ => t ^ (2 * N))
    have hcont_at : ContinuousAt (fun t : ℝ => t ^ (2 * N)) 1 :=
      hcont.continuousAt
    simpa [Function.comp, one_pow] using hcont_at.tendsto.comp hx_tendsto
  have hmem : Set.Ioi (1 / 2 : ℝ) ∈ 𝓝 (1 : ℝ) := by
    refine isOpen_Ioi.mem_nhds ?_
    norm_num
  have h_event : ∀ᶠ k in atTop, (x k) ^ (2 * N) ∈ Set.Ioi (1 / 2 : ℝ) :=
    hxpow_tendsto.eventually_mem hmem
  rcases (eventually_atTop.1 h_event) with ⟨K, hK⟩
  refine ⟨x K, ?_, ?_⟩
  · have hpos : 0 < 1 / ((K : ℝ) + 1) := by
      have hk : 0 < (K : ℝ) + 1 := by nlinarith
      exact one_div_pos.mpr hk
    have hxlt : x K < 1 := by
      simpa [x] using (sub_lt_self (1 : ℝ) hpos)
    have hle : 1 / ((K : ℝ) + 1) ≤ (1 : ℝ) := by
      have hk : (1 : ℝ) ≤ (K : ℝ) + 1 := by nlinarith
      have hle' : (1 : ℝ) / ((K : ℝ) + 1) ≤ (1 : ℝ) / 1 :=
        one_div_le_one_div_of_le (by norm_num) hk
      simpa using hle'
    have hxnonneg : 0 ≤ x K := by
      have : (0 : ℝ) ≤ 1 - 1 / ((K : ℝ) + 1) := by linarith
      simpa [x] using this
    have hxgt_neg1 : -1 < x K := by linarith
    exact ⟨hxgt_neg1, hxlt⟩
  · have hK' : (x K) ^ (2 * N) ∈ Set.Ioi (1 / 2 : ℝ) := hK K (le_rfl)
    simpa [Set.mem_Ioi] using hK'

/-- Example 6.1.8: The sequence of even powers `fₙ(x) = x^(2 n)` converges
pointwise on `[-1,1]` to the function that is `1` at the endpoints and `0`
elsewhere, but this convergence is not uniform on the whole interval. -/
lemma not_uniformConverges_pow_even_on_unit_interval :
    ¬ uniformConverges
      (fun n : ℕ => fun x : {x // x ∈ Set.Icc (-1 : ℝ) 1} => (x : ℝ) ^ (2 * n))
      (fun x : {x // x ∈ Set.Icc (-1 : ℝ) 1} =>
        if (x : ℝ) = 1 ∨ (x : ℝ) = -1 then (1 : ℝ) else 0) := by
  intro h
  have hε := h (1 / 2 : ℝ) (by norm_num)
  rcases hε with ⟨N, hN⟩
  rcases exists_x_pow_even_ge_half N with ⟨x, hx, hxpow⟩
  have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  let x' : {x // x ∈ Set.Icc (-1 : ℝ) 1} := ⟨x, hxIcc⟩
  have hxne1 : (x : ℝ) ≠ 1 := ne_of_lt hx.2
  have hxne_neg1 : (x : ℝ) ≠ -1 := ne_of_gt hx.1
  have hxg : (if (x' : ℝ) = 1 ∨ (x' : ℝ) = -1 then (1 : ℝ) else 0) = 0 := by
    have hxne1' : (x' : ℝ) ≠ 1 := by simpa using hxne1
    have hxne_neg1' : (x' : ℝ) ≠ -1 := by simpa using hxne_neg1
    have hnot : ¬ ((x' : ℝ) = 1 ∨ (x' : ℝ) = -1) := by
      intro h
      rcases h with h1 | h2
      · exact hxne1' h1
      · exact hxne_neg1' h2
    simp [hnot]
  have hbound : |(x : ℝ) ^ (2 * N)| < (1 / 2 : ℝ) := by
    simpa [hxg] using hN N (le_rfl) x'
  have hnonneg : 0 ≤ (x : ℝ) ^ (2 * N) := by
    have hx2_nonneg : 0 ≤ (x : ℝ) ^ 2 := by
      simpa [pow_two] using sq_nonneg (x : ℝ)
    have hpow_nonneg : 0 ≤ ((x : ℝ) ^ 2) ^ N := by
      exact pow_nonneg hx2_nonneg N
    simpa [pow_mul] using hpow_nonneg
  have hlt : (x : ℝ) ^ (2 * N) < (1 / 2 : ℝ) := by
    simpa [abs_of_nonneg hnonneg] using hbound
  linarith

/-- Example 6.1.8 (continued): If we restrict to `[-a, a]` with `0 < a < 1`,
then the even powers `fₙ(x) = x^(2 n)` converge uniformly to `0` on that
smaller interval. -/
lemma uniformConverges_pow_even_on_subinterval {a : ℝ} (ha_pos : 0 < a)
    (ha_lt_one : a < 1) :
    uniformConverges
      (fun n : ℕ => fun x : {x // x ∈ Set.Icc (-a : ℝ) a} => (x : ℝ) ^ (2 * n))
      (fun _ => 0) := by
  intro ε hε
  have ha_abs : |a| < 1 := by
    have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
    simpa [abs_of_nonneg ha_nonneg] using ha_lt_one
  have ha2_nonneg : 0 ≤ a ^ 2 := by
    simpa [pow_two] using sq_nonneg a
  have ha2_lt1 : a ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one a).2 ha_abs
  have hpow : Tendsto (fun n : ℕ => (a ^ 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha2_nonneg ha2_lt1
  have hpow' : Tendsto (fun n : ℕ => a ^ (2 * n)) atTop (𝓝 0) := by
    simpa [pow_mul] using hpow
  have hmem : Set.Iio ε ∈ 𝓝 (0 : ℝ) := by
    refine isOpen_Iio.mem_nhds ?_
    simpa using hε
  have h_event : ∀ᶠ n in atTop, a ^ (2 * n) ∈ Set.Iio ε :=
    hpow'.eventually_mem hmem
  rcases (eventually_atTop.1 h_event) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x
  have hN' : a ^ (2 * n) < ε := by
    have hmem' : a ^ (2 * n) ∈ Set.Iio ε := hN n hn
    simpa [Set.mem_Iio] using hmem'
  have hxabs : |(x : ℝ)| ≤ a := by
    have hx : (x : ℝ) ∈ Set.Icc (-a) a := x.property
    exact (abs_le).2 ⟨hx.1, hx.2⟩
  have hpowle : |(x : ℝ) ^ (2 * n)| ≤ a ^ (2 * n) := by
    have hpowle' : |(x : ℝ)| ^ (2 * n) ≤ a ^ (2 * n) :=
      pow_le_pow_left₀ (abs_nonneg _) hxabs (2 * n)
    simpa [abs_pow] using hpowle'
  have hlt : |(x : ℝ) ^ (2 * n)| < ε := lt_of_le_of_lt hpowle hN'
  simpa [sub_zero] using hlt

/-- Definition 6.1.9: For a bounded function `f : S → ℝ`, the uniform norm
is the supremum of the absolute value of `f` over the set `S`; this coincides
with the usual sup (or infinity) norm. -/
noncomputable def uniformNormOn {S : Type u} (A : Set S) (f : S → ℝ) : ℝ :=
  sSup ((fun x => |f x|) '' A)

/-- Proposition 6.1.10: A sequence of bounded functions `fₙ : S → ℝ`
converges uniformly to `f : S → ℝ` if and only if the uniform norms of the
difference `fₙ - f` converge to `0`. -/
theorem uniformConverges_iff_uniformNormOn_tendsto_zero {S : Type u}
    (f : ℕ → S → ℝ) (g : S → ℝ)
    (hbounded : ∀ n, BddAbove ((fun x => |f n x - g x|) '' (Set.univ : Set S))) :
    uniformConverges f g ↔
      Tendsto (fun n => uniformNormOn (Set.univ : Set S) (fun x => f n x - g x))
        atTop (𝓝 0) := by
  have abs_sub_le_uniformNormOn_univ :
      ∀ n x, |f n x - g x| ≤
        uniformNormOn (Set.univ : Set S) (fun x => f n x - g x) := by
    intro n x
    unfold uniformNormOn
    refine le_csSup (hbounded n) ?_
    refine ⟨x, ?_, rfl⟩
    simp
  have uniformNormOn_le_of_forall_abs_le :
      ∀ n ε, 0 ≤ ε → (∀ x, |f n x - g x| ≤ ε) →
        uniformNormOn (Set.univ : Set S) (fun x => f n x - g x) ≤ ε := by
    intro n ε hε hbound
    unfold uniformNormOn
    refine Real.sSup_le ?_ hε
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hbound x
  have uniformNormOn_nonneg :
      ∀ n, 0 ≤ uniformNormOn (Set.univ : Set S) (fun x => f n x - g x) := by
    intro n
    unfold uniformNormOn
    refine Real.sSup_nonneg ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact abs_nonneg _
  constructor
  · intro hconv
    refine (Metric.tendsto_nhds.2 ?_)
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    rcases hconv (ε / 2) hε2 with ⟨N, hN⟩
    refine (eventually_atTop.2 ?_)
    refine ⟨N, ?_⟩
    intro n hn
    have hbound :
        uniformNormOn (Set.univ : Set S) (fun x => f n x - g x) ≤ ε / 2 := by
      refine uniformNormOn_le_of_forall_abs_le n (ε / 2) (le_of_lt hε2) ?_
      intro x
      exact le_of_lt (hN n hn x)
    have hnonneg := uniformNormOn_nonneg n
    have hlt : uniformNormOn (Set.univ : Set S) (fun x => f n x - g x) < ε := by
      have hhalf : ε / 2 < ε := by linarith
      exact lt_of_le_of_lt hbound hhalf
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hlt
  · intro htend ε hε
    have h_event :
        ∀ᶠ n in atTop,
          dist (uniformNormOn (Set.univ : Set S) (fun x => f n x - g x)) 0 < ε :=
      (Metric.tendsto_nhds.1 htend) ε hε
    rcases (eventually_atTop.1 h_event) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn x
    have hdist :
        dist (uniformNormOn (Set.univ : Set S) (fun x => f n x - g x)) 0 < ε :=
      hN n hn
    have hnonneg := uniformNormOn_nonneg n
    have hlt :
        uniformNormOn (Set.univ : Set S) (fun x => f n x - g x) < ε := by
      simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hdist
    have hbound :
        |f n x - g x| ≤
          uniformNormOn (Set.univ : Set S) (fun x => f n x - g x) :=
      abs_sub_le_uniformNormOn_univ n x
    exact lt_of_le_of_lt hbound hlt

/-- Example 6.1.11: For `fₙ(x) = (n x + \sin (n x^2)) / n` on `[0,1]`,
the sequence converges uniformly to the identity function `x ↦ x`. -/
theorem uniformConverges_nat_mul_add_sin_div_nat :
    uniformConverges
      (fun n : ℕ => fun x : {x // x ∈ Set.Icc (0 : ℝ) 1} =>
        (((Nat.succ n : ℝ) * (x : ℝ) +
            Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ))) /
          (Nat.succ n : ℝ)))
      (fun x : {x // x ∈ Set.Icc (0 : ℝ) 1} => (x : ℝ)) := by
  intro ε hε
  rcases (exists_nat_one_div_lt (K := ℝ) hε) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x
  have hn1pos : 0 < (Nat.succ n : ℝ) := by
    exact_mod_cast (Nat.succ_pos n)
  have hn1ne : (Nat.succ n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  have hdiff :
      |(((Nat.succ n : ℝ) * (x : ℝ) +
            Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ))) /
          (Nat.succ n : ℝ) - (x : ℝ))|
        = |Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ))| / (↑n + 1 : ℝ) := by
    have hdiff' :
        (((Nat.succ n : ℝ) * (x : ℝ) +
              Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ))) /
            (Nat.succ n : ℝ) - (x : ℝ))
          = Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ)) /
            (Nat.succ n : ℝ) := by
      field_simp [hn1ne]
      ring
    have hn1pos' : 0 < (↑n + 1 : ℝ) := by
      simpa using hn1pos
    calc
      |(((Nat.succ n : ℝ) * (x : ℝ) +
            Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ))) /
          (Nat.succ n : ℝ) - (x : ℝ))|
          = |Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ)) /
              (Nat.succ n : ℝ)| := by
            simpa using congrArg abs hdiff'
      _ = |Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ))| /
            |(Nat.succ n : ℝ)| := by
            simp [abs_div]
      _ = |Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ))| / |(↑n + 1 : ℝ)| := by
            simp [Nat.cast_succ]
      _ = |Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ))| / (↑n + 1 : ℝ) := by
            simp [abs_of_pos hn1pos']
  have hsinle :
      |Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ))| ≤ (1 : ℝ) := by
    simpa using
      (Real.abs_sin_le_one ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ)))
  have hbound :
      |(((Nat.succ n : ℝ) * (x : ℝ) +
            Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ))) /
          (Nat.succ n : ℝ) - (x : ℝ))|
        ≤ 1 / (Nat.succ n : ℝ) := by
    have hinv_nonneg : 0 ≤ (Nat.succ n : ℝ)⁻¹ := by
      exact inv_nonneg.mpr (le_of_lt hn1pos)
    have hmul :
        |Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ))| *
            (Nat.succ n : ℝ)⁻¹ ≤
          (1 : ℝ) * (Nat.succ n : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hsinle hinv_nonneg
    have hdiv :
        |Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ))| /
            (Nat.succ n : ℝ) ≤
          1 / (Nat.succ n : ℝ) := by
      simpa [div_eq_mul_inv] using hmul
    have hdiv' :
        |Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ))| /
            (↑n + 1 : ℝ) ≤
          1 / (↑n + 1 : ℝ) := by
      simpa [Nat.cast_succ] using hdiv
    calc
      |(((Nat.succ n : ℝ) * (x : ℝ) +
            Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ))) /
          (Nat.succ n : ℝ) - (x : ℝ))|
          = |Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ))| / (↑n + 1 : ℝ) := hdiff
      _ ≤ 1 / (↑n + 1 : ℝ) := hdiv'
      _ = 1 / (Nat.succ n : ℝ) := by
        simp [Nat.cast_succ]
  have hmono :
      1 / (Nat.succ n : ℝ) ≤ 1 / (Nat.succ N : ℝ) := by
    have hle : (Nat.succ N : ℝ) ≤ (Nat.succ n : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ hn)
    have hNpos : 0 < (Nat.succ N : ℝ) := by
      exact_mod_cast (Nat.succ_pos N)
    exact one_div_le_one_div_of_le hNpos hle
  have hbound' :
      |(((Nat.succ n : ℝ) * (x : ℝ) +
            Real.sin ((Nat.succ n : ℝ) * (x : ℝ) ^ (2 : ℕ))) /
          (Nat.succ n : ℝ) - (x : ℝ))|
        ≤ 1 / (Nat.succ N : ℝ) := by
    exact le_trans hbound hmono
  exact lt_of_le_of_lt hbound' (by simpa using hN)

/-- Definition 6.1.12: A sequence of bounded functions `fₙ : S → ℝ` is
uniformly Cauchy (Cauchy in the uniform norm) if for every `ε > 0` there
exists `N` such that for all `m, k ≥ N`, the uniform norm of `fₘ - fₖ` on `S`
is less than `ε`. -/
def uniformlyCauchy {S : Type u} (f : ℕ → S → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ k ≥ N,
    uniformNormOn (Set.univ : Set S) (fun x => f m x - f k x) < ε

/-- Proposition 6.1.13: For bounded functions `fₙ : S → ℝ`, the sequence is
uniformly Cauchy (Cauchy in the uniform norm) if and only if there exists a
function `f : S → ℝ` such that `fₙ` converges uniformly to `f`. -/
theorem uniformlyCauchy_iff_exists_uniformLimit {S : Type u} (f : ℕ → S → ℝ)
    (hbounded : ∀ n, BddAbove ((fun x => |f n x|) '' (Set.univ : Set S))) :
    uniformlyCauchy f ↔ ∃ g : S → ℝ, uniformConverges f g := by
  classical
  constructor
  · intro hC
    have bddAbove_abs_sub_univ :
        ∀ m k, BddAbove ((fun x => |f m x - f k x|) '' (Set.univ : Set S)) := by
      intro m k
      rcases hbounded m with ⟨Mm, hMm⟩
      rcases hbounded k with ⟨Mk, hMk⟩
      refine ⟨Mm + Mk, ?_⟩
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hm : |f m x| ≤ Mm := hMm ⟨x, by simp, rfl⟩
      have hk : |f k x| ≤ Mk := hMk ⟨x, by simp, rfl⟩
      have hsum : |f m x - f k x| ≤ |f m x| + |f k x| := by
        simpa using (abs_sub_le (f m x) 0 (f k x))
      linarith
    have abs_sub_le_uniformNormOn_univ :
        ∀ m k x, |f m x - f k x| ≤
          uniformNormOn (Set.univ : Set S) (fun x => f m x - f k x) := by
      intro m k x
      unfold uniformNormOn
      refine le_csSup (bddAbove_abs_sub_univ m k) ?_
      refine ⟨x, by simp, rfl⟩
    have hpoint_cauchy : ∀ x, CauchySeq (fun n => f n x) := by
      intro x
      refine (Metric.cauchySeq_iff).2 ?_
      intro ε hε
      rcases hC ε hε with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro m hm k hk
      have hmk' :
          uniformNormOn (Set.univ : Set S) (fun x => f m x - f k x) < ε :=
        hN m hm k hk
      have hle : |f m x - f k x| ≤
          uniformNormOn (Set.univ : Set S) (fun x => f m x - f k x) :=
        abs_sub_le_uniformNormOn_univ m k x
      have hlt : |f m x - f k x| < ε := lt_of_le_of_lt hle hmk'
      simpa [Real.dist_eq] using hlt
    have hpoint :
        ∀ x, ∃ l, Tendsto (fun n => f n x) atTop (𝓝 l) := by
      intro x
      exact cauchySeq_tendsto_of_complete (hpoint_cauchy x)
    choose g hg using hpoint
    refine ⟨g, ?_⟩
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    rcases hC (ε / 2) hε2 with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm x
    have h_event :
        ∀ᶠ k in atTop, f k x ∈ Metric.closedBall (f m x) (ε / 2) := by
      refine (eventually_atTop.2 ?_)
      refine ⟨N, ?_⟩
      intro k hk
      have hmk' :
          uniformNormOn (Set.univ : Set S) (fun x => f m x - f k x) < ε / 2 :=
        hN m hm k hk
      have hle : |f m x - f k x| ≤
          uniformNormOn (Set.univ : Set S) (fun x => f m x - f k x) :=
        abs_sub_le_uniformNormOn_univ m k x
      have hlt : |f m x - f k x| < ε / 2 := lt_of_le_of_lt hle hmk'
      have hdist : dist (f k x) (f m x) < ε / 2 := by
        have hdist' : dist (f m x) (f k x) < ε / 2 := by
          simpa [Real.dist_eq] using hlt
        simpa [dist_comm] using hdist'
      have hdist_le : dist (f k x) (f m x) ≤ ε / 2 := le_of_lt hdist
      simpa [Metric.mem_closedBall] using hdist_le
    have hxmem : g x ∈ Metric.closedBall (f m x) (ε / 2) := by
      have hclosed : IsClosed (Metric.closedBall (f m x) (ε / 2)) :=
        Metric.isClosed_closedBall
      exact hclosed.mem_of_tendsto (hg x) h_event
    have hdist' : dist (f m x) (g x) ≤ ε / 2 := by
      have hdist : dist (g x) (f m x) ≤ ε / 2 := by
        simpa [Metric.mem_closedBall] using hxmem
      simpa [dist_comm] using hdist
    have hle : |f m x - g x| ≤ ε / 2 := by
      simpa [Real.dist_eq] using hdist'
    have hhalf : ε / 2 < ε := by linarith
    exact lt_of_le_of_lt hle hhalf
  · rintro ⟨g, hconv⟩ ε hε
    have hε4 : 0 < ε / 4 := by linarith
    rcases hconv (ε / 4) hε4 with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm k hk
    have hbound : ∀ x, |f m x - f k x| < ε / 2 := by
      intro x
      have hm' : |f m x - g x| < ε / 4 := hN m hm x
      have hk' : |f k x - g x| < ε / 4 := hN k hk x
      have hsum : |f m x - f k x| ≤ |f m x - g x| + |f k x - g x| := by
        simpa [abs_sub_comm] using (abs_sub_le (f m x) (g x) (f k x))
      have hsum_lt : |f m x - g x| + |f k x - g x| < ε / 2 := by linarith
      exact lt_of_le_of_lt hsum hsum_lt
    have hsup :
        uniformNormOn (Set.univ : Set S) (fun x => f m x - f k x) ≤ ε / 2 := by
      unfold uniformNormOn
      refine Real.sSup_le ?_ (by linarith)
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact le_of_lt (hbound x)
    have hhalf : ε / 2 < ε := by linarith
    exact lt_of_le_of_lt hsup hhalf

end Section01
end Chap06
