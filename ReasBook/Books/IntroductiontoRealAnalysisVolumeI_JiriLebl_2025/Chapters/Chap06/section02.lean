/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import Mathlib
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap03.section02
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap05.section01
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap05.section02

section Chap06
section Section02

open Filter
open MeasureTheory
open BigOperators
open scoped Topology BigOperators

noncomputable section

/-- Example 6.2.1: For each `n`, define `fₙ : [0,1] → ℝ` by
`fₙ(x) = 1 - n x` when `x < 1 / n` and `fₙ(x) = 0` when `x ≥ 1 / n`.
Each `fₙ` is continuous, the pointwise limit is the function that is `1`
at `0` and `0` for `x > 0`, and this limit is not continuous at `0`. -/
def example6_2_1_fn (n : ℕ) (x : ℝ) : ℝ :=
  if x < (1 : ℝ) / (Nat.succ n) then 1 - (Nat.succ n : ℝ) * x else 0

/-- The pointwise limit function in Example 6.2.1, equal to `1` at `0` and
`0` elsewhere. -/
def example6_2_1_limit (x : ℝ) : ℝ :=
  if x = 0 then 1 else 0

/-- The sequence `example6_2_1_fn n` consists of continuous functions. -/
lemma example6_2_1_fn_continuous (n : ℕ) :
    Continuous fun x : ℝ => example6_2_1_fn n x := by
  classical
  have h_boundary :
      ∀ x ∈ frontier {x : ℝ | x < (1 : ℝ) / (Nat.succ n)},
        (1 - (Nat.succ n : ℝ) * x) = 0 := by
    intro x hx
    have hx' : x = (1 : ℝ) / (Nat.succ n) := by
      have hx' : x ∈ frontier (Set.Iio ((1 : ℝ) / (Nat.succ n))) := by
        simpa [Set.Iio] using hx
      simpa [frontier_Iio] using hx'
    subst hx'
    have hne : (↑n + 1 : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero n)
    simp [hne]
  have hf : Continuous fun x : ℝ => 1 - (Nat.succ n : ℝ) * x := by
    simpa using (continuous_const.sub (continuous_const.mul continuous_id))
  have hg : Continuous fun _x : ℝ => (0 : ℝ) := continuous_const
  simpa [example6_2_1_fn] using
    (Continuous.if (p := fun x : ℝ => x < (1 : ℝ) / (Nat.succ n))
      (f := fun x : ℝ => 1 - (Nat.succ n : ℝ) * x)
      (g := fun _x : ℝ => (0 : ℝ))
      h_boundary hf hg)

/-- For any `x > 0`, the sequence `example6_2_1_fn n x` converges to `0`. -/
lemma tendsto_example6_2_1_fn_of_pos {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => example6_2_1_fn n x) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hx
  have h_eventually : ∀ᶠ n in atTop, example6_2_1_fn n x = 0 := by
    refine (eventually_atTop.2 ?_)
    refine ⟨N, ?_⟩
    intro n hn
    have hpos : (0 : ℝ) < (Nat.succ N : ℝ) := by
      exact_mod_cast (Nat.succ_pos N)
    have hle : (Nat.succ N : ℝ) ≤ (Nat.succ n : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ hn)
    have hdiv : 1 / (Nat.succ n : ℝ) ≤ 1 / (Nat.succ N : ℝ) :=
      one_div_le_one_div_of_le hpos hle
    have hxge : 1 / (Nat.succ n : ℝ) ≤ x := by
      refine le_trans hdiv ?_
      exact le_of_lt (by simpa using hN)
    have hxlt : ¬ x < (1 : ℝ) / (Nat.succ n) := by
      exact not_lt.mpr hxge
    have hxlt' : ¬ x < (↑n + 1 : ℝ)⁻¹ := by
      simpa using hxlt
    have himp : x < (↑n + 1 : ℝ)⁻¹ → 1 - (↑n + 1 : ℝ) * x = 0 := by
      intro hx
      exact (hxlt' hx).elim
    simpa [example6_2_1_fn] using himp
  refine (tendsto_congr' h_eventually).2 ?_
  simp

/-- At `x = 0`, the sequence `example6_2_1_fn n 0` converges to `1`. -/
lemma tendsto_example6_2_1_fn_zero :
    Tendsto (fun n : ℕ => example6_2_1_fn n 0) atTop (𝓝 1) := by
  have h_eq : ∀ n : ℕ, example6_2_1_fn n 0 = (1 : ℝ) := by
    intro n
    have hpos : (0 : ℝ) < (1 : ℝ) / (Nat.succ n : ℝ) := by
      have hpos' : (0 : ℝ) < (Nat.succ n : ℝ) := by
        exact_mod_cast (Nat.succ_pos n)
      exact one_div_pos.mpr hpos'
    unfold example6_2_1_fn
    split_ifs
    · simp
  refine (tendsto_congr h_eq).2 ?_
  simp

/-- The pointwise limit of `example6_2_1_fn` on `[0, 1]` is the function that
is `1` at `0` and `0` elsewhere, and this limit function is not continuous at
`0`. -/
theorem example6_2_1_limit_not_continuous :
    (Tendsto (fun n : ℕ => example6_2_1_fn n 0) atTop
        (𝓝 (example6_2_1_limit 0)))
    ∧ (∀ x > 0,
        Tendsto (fun n : ℕ => example6_2_1_fn n x) atTop
      (𝓝 (example6_2_1_limit x)))
    ∧ ¬ ContinuousAt example6_2_1_limit 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [example6_2_1_limit] using tendsto_example6_2_1_fn_zero
  · intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    simpa [example6_2_1_limit, hx0] using
      (tendsto_example6_2_1_fn_of_pos (x := x) hx)
  · intro hcont
    have hseq :
        Tendsto (fun n : ℕ => (1 : ℝ) / (Nat.succ n)) atTop (𝓝 (0 : ℝ)) := by
      simpa using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 (0 : ℝ)))
    have hlim :
        Tendsto (fun n : ℕ => example6_2_1_limit ((1 : ℝ) / (Nat.succ n)))
          atTop (𝓝 (example6_2_1_limit 0)) := by
      exact hcont.tendsto.comp hseq
    have hlim0 :
        Tendsto (fun n : ℕ => example6_2_1_limit ((1 : ℝ) / (Nat.succ n)))
          atTop (𝓝 (0 : ℝ)) := by
      have h_eq :
          ∀ n : ℕ, example6_2_1_limit ((1 : ℝ) / (Nat.succ n)) = (0 : ℝ) := by
        intro n
        have hne : (1 : ℝ) / (Nat.succ n : ℝ) ≠ 0 := by
          have hne' : (Nat.succ n : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.succ_ne_zero n)
          exact one_div_ne_zero hne'
        unfold example6_2_1_limit
        exact if_neg hne
      refine (tendsto_congr h_eq).2 ?_
      simp
    have h_eq : example6_2_1_limit 0 = (0 : ℝ) :=
      tendsto_nhds_unique hlim hlim0
    simp [example6_2_1_limit] at h_eq

/-- Theorem 6.2.2: If `fₙ : S → ℝ` is a sequence of continuous functions that
converges uniformly to `f : S → ℝ`, then `f` is continuous. -/
theorem continuous_of_uniformLimit {S : Set ℝ} {f : S → ℝ} {fSeq : ℕ → S → ℝ}
    (hcont : ∀ n, Continuous (fSeq n))
    (hlim : TendstoUniformly fSeq f atTop) :
    Continuous f := by
  have hc : ∃ᶠ n in atTop, Continuous (fSeq n) := by
    exact (Filter.Eventually.of_forall hcont).frequently
  exact hlim.continuous hc

/-- Example 6.2.3: The sequence of piecewise linear functions
`fₙ : [0,1] → ℝ` given by `fₙ(0) = 0`, `fₙ(x) = (n + 1) - (n + 1)² x`
for `0 < x < 1 / (n + 1)`, and `fₙ(x) = 0` for `x ≥ 1 / (n + 1)` is
Riemann integrable with integral `1 / 2`.  The pointwise limit on `[0,1]`
is the zero function, so `lim_{n → ∞} ∫₀¹ fₙ = 1/2` while
`∫₀¹ (lim_{n → ∞} fₙ) = 0`. -/
def example6_2_3_fn (n : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then 0
  else
    if x < (1 : ℝ) / (Nat.succ n) then
      (Nat.succ n : ℝ) - (Nat.succ n : ℝ) ^ 2 * x
    else 0

/-- Each `example6_2_3_fn n` has integral `1/2` on the interval `(0, 1]`. -/
lemma example6_2_3_integral_half (n : ℕ) :
    ∫ x in (0)..1, example6_2_3_fn n x = (1 : ℝ) / 2 := by
  set N : ℝ := (Nat.succ n : ℝ)
  set c : ℝ := (1 : ℝ) / N
  have hN : N ≠ 0 := by
    have hN' : (Nat.succ n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero n)
    simpa [N] using hN'
  let g : ℝ → ℝ := fun x => if x < c then N - N ^ 2 * x else 0
  have h_eq_integral :
      ∫ x in (0)..1, example6_2_3_fn n x = ∫ x in (0)..1, g x := by
    have hne : ∀ᵐ x ∂volume, x ≠ (0 : ℝ) := by
      simp [ae_iff, measure_singleton]
    have h_ae :
        ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) 1 →
          example6_2_3_fn n x = g x := by
      refine hne.mono ?_
      intro x hx _hxIcc
      simp [example6_2_3_fn, g, hx, N, c]
    exact intervalIntegral.integral_congr_ae h_ae
  have hc0 : (0 : ℝ) ≤ c := by
    have hNpos : (0 : ℝ) < N := by
      have hNpos' : (0 : ℝ) < (Nat.succ n : ℝ) := by
        exact_mod_cast (Nat.succ_pos n)
      simpa [N] using hNpos'
    exact one_div_nonneg.mpr (le_of_lt hNpos)
  have hc1 : c ≤ (1 : ℝ) := by
    have hN1 : (1 : ℝ) ≤ N := by
      simp [N]
    have h : (1 : ℝ) / N ≤ (1 : ℝ) / (1 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hN1
    simpa [c] using h
  have h_eq_on_left :
      Set.EqOn g (fun x => N - N ^ 2 * x) (Set.uIoc (0 : ℝ) c) := by
    intro x hx
    have hx' : x ∈ Set.Ioc (0 : ℝ) c := by
      simpa [Set.uIoc_of_le hc0] using hx
    have hxle : x ≤ c := hx'.2
    have hxlt_or_eq : x < c ∨ x = c := lt_or_eq_of_le hxle
    cases hxlt_or_eq with
    | inl hlt =>
        simp [g, hlt]
    | inr hEq =>
        subst hEq
        have hcalc : N - N ^ 2 * c = 0 := by
          simp [c]
          field_simp [hN]
          ring_nf
        calc
          g c = 0 := by simp [g]
          _ = N - N ^ 2 * c := by
            symm
            exact hcalc
  have h_eq_on_right :
      Set.EqOn g (fun _x => (0 : ℝ)) (Set.uIoc c 1) := by
    intro x hx
    have hx' : x ∈ Set.Ioc c (1 : ℝ) := by
      simpa [Set.uIoc_of_le hc1] using hx
    have hxge : c ≤ x := le_of_lt hx'.1
    have hxlt : ¬ x < c := not_lt.mpr hxge
    simp [g, hxlt]
  have h_lin_int : IntervalIntegrable (fun x => N - N ^ 2 * x) volume (0 : ℝ) c := by
    have hcont : Continuous (fun x => N - N ^ 2 * x) := by
      fun_prop
    simpa using (hcont.intervalIntegrable (a := (0 : ℝ)) (b := c))
  have h0 : IntervalIntegrable g volume (0 : ℝ) c := by
    exact (intervalIntegrable_congr (f := g)
      (g := fun x => N - N ^ 2 * x) h_eq_on_left).2 h_lin_int
  have h_const_int : IntervalIntegrable (fun _x => (0 : ℝ)) volume c 1 := by
    simp
  have h1 : IntervalIntegrable g volume c 1 := by
    exact (intervalIntegrable_congr (f := g)
      (g := fun _x => (0 : ℝ)) h_eq_on_right).2 h_const_int
  have h_int_left : ∫ x in (0 : ℝ)..c, g x = (1 : ℝ) / 2 := by
    have h_lin : ∫ x in (0 : ℝ)..c, g x =
        ∫ x in (0 : ℝ)..c, (N - N ^ 2 * x) := by
      refine intervalIntegral.integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      exact h_eq_on_left hx
    have h_lin_val :
        ∫ x in (0 : ℝ)..c, (N - N ^ 2 * x) = (1 : ℝ) / 2 := by
      have h1' : IntervalIntegrable (fun _x : ℝ => N) volume (0 : ℝ) c := by
        simp
      have h2' : IntervalIntegrable (fun x : ℝ => N ^ 2 * x) volume (0 : ℝ) c := by
        have hcont : Continuous (fun x : ℝ => N ^ 2 * x) := by
          fun_prop
        simpa using (hcont.intervalIntegrable (a := (0 : ℝ)) (b := c))
      calc
        ∫ x in (0 : ℝ)..c, (N - N ^ 2 * x)
            = (∫ x in (0 : ℝ)..c, (N : ℝ)) - ∫ x in (0 : ℝ)..c, (N ^ 2 * x) := by
              simpa using (intervalIntegral.integral_sub h1' h2')
        _ = (c - 0) * N - (N ^ 2) * ((c ^ 2 - 0 ^ 2) / 2) := by
              have h_int : ∫ x in (0 : ℝ)..c, N ^ 2 * x = N ^ 2 * (c ^ 2 / 2) := by
                calc
                  ∫ x in (0 : ℝ)..c, N ^ 2 * x = (N ^ 2) * ∫ x in (0 : ℝ)..c, x := by
                    simpa using
                      (intervalIntegral.integral_const_mul (μ := volume)
                        (a := (0 : ℝ)) (b := c)
                        (r := (N ^ 2)) (f := fun x => x))
                  _ = N ^ 2 * (c ^ 2 / 2) := by
                    simp [integral_id]
              simp [h_int]
        _ = (1 : ℝ) / 2 := by
              simp [c]
              field_simp [hN]
              ring
    simpa [h_lin] using h_lin_val
  have h_int_right : ∫ x in c..1, g x = (0 : ℝ) := by
    calc
      ∫ x in c..1, g x = ∫ x in c..1, (0 : ℝ) := by
        refine intervalIntegral.integral_congr_ae ?_
        refine Filter.Eventually.of_forall ?_
        intro x hx
        exact h_eq_on_right hx
      _ = 0 := by simp
  have h_split :
      ∫ x in (0 : ℝ)..1, g x =
        (∫ x in (0 : ℝ)..c, g x) + ∫ x in c..1, g x := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals h0 h1
  calc
    ∫ x in (0 : ℝ)..1, example6_2_3_fn n x
        = ∫ x in (0 : ℝ)..1, g x := h_eq_integral
    _ = (∫ x in (0 : ℝ)..c, g x) + ∫ x in c..1, g x := h_split
    _ = (1 : ℝ) / 2 := by simp [h_int_left, h_int_right]

/-- For any `x ∈ [0,1]`, the sequence `example6_2_3_fn n x` converges to `0`. -/
lemma example6_2_3_pointwise_limit_zero {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => example6_2_3_fn n x) atTop (𝓝 0) := by
  by_cases hx0 : x = 0
  · subst hx0
    have h_eq : ∀ n : ℕ, example6_2_3_fn n 0 = (0 : ℝ) := by
      intro n
      simp [example6_2_3_fn]
    refine (tendsto_congr h_eq).2 ?_
    simp
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hxpos
    have h_eventually : ∀ᶠ n in atTop, example6_2_3_fn n x = 0 := by
      refine (eventually_atTop.2 ?_)
      refine ⟨N, ?_⟩
      intro n hn
      have hpos : (0 : ℝ) < (Nat.succ N : ℝ) := by
        exact_mod_cast (Nat.succ_pos N)
      have hle : (Nat.succ N : ℝ) ≤ (Nat.succ n : ℝ) := by
        exact_mod_cast (Nat.succ_le_succ hn)
      have hdiv : 1 / (Nat.succ n : ℝ) ≤ 1 / (Nat.succ N : ℝ) :=
        one_div_le_one_div_of_le hpos hle
      have hxge : 1 / (Nat.succ n : ℝ) ≤ x := by
        refine le_trans hdiv ?_
        exact le_of_lt (by simpa using hN)
      have hxlt : ¬ x < (1 : ℝ) / (Nat.succ n) := not_lt.mpr hxge
      have hxlt' : ¬ x < (↑n + 1 : ℝ)⁻¹ := by
        simpa using hxlt
      simp [example6_2_3_fn, hx0, hxlt']
    refine (tendsto_congr' h_eventually).2 ?_
    simp

/-- The integrals of `example6_2_3_fn n` converge to `1/2`, while the
integral of the pointwise limit is `0`, showing that pointwise convergence
alone does not allow interchanging limit and integral. -/
theorem example6_2_3_integral_limit_ne_limit_integral :
    Tendsto (fun n : ℕ => ∫ x in (0)..1, example6_2_3_fn n x)
      atTop (𝓝 ((1 : ℝ) / 2))
    ∧ (∀ x ∈ Set.Icc (0 : ℝ) 1,
        Tendsto (fun n : ℕ => example6_2_3_fn n x) atTop (𝓝 0))
    ∧ ((1 : ℝ) / 2 ≠ (∫ _ in (0)..1, (0 : ℝ))) := by
  refine ⟨?_, ?_, ?_⟩
  · have h_eq : ∀ n : ℕ,
        ∫ x in (0)..1, example6_2_3_fn n x = (1 : ℝ) / 2 := by
      intro n
      exact example6_2_3_integral_half n
    refine (tendsto_congr h_eq).2 ?_
    simp
  · intro x hx
    exact example6_2_3_pointwise_limit_zero (x := x) hx
  · simp

/-- Theorem 6.2.4: If `fₙ : [a, b] → ℝ` is a sequence of Riemann integrable
functions converging uniformly to `f : [a, b] → ℝ`, then `f` is Riemann
integrable and the integral of the limit equals the limit of the integrals. -/
theorem integral_interval_tendsto_of_uniform_limit {a b : ℝ}
    {f : ℝ → ℝ} {fSeq : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (fSeq n) volume a b)
    (hlim : TendstoUniformlyOn fSeq f atTop (Set.Icc a b))
    (hab : a ≤ b) :
    IntervalIntegrable f volume a b
      ∧ Tendsto (fun n : ℕ => ∫ x in a..b, fSeq n x) atTop (𝓝 (∫ x in a..b, f x)) := by
  classical
  have hsub : Set.uIoc a b ⊆ Set.Icc a b := by
    have hsub' : Set.uIoc a b ⊆ Set.uIcc a b := Set.uIoc_subset_uIcc
    simpa [Set.uIcc_of_le hab] using hsub'
  have hlim' : TendstoUniformlyOn fSeq f atTop (Set.uIoc a b) :=
    hlim.mono hsub
  have h_eventually :
      ∀ᶠ n in atTop, ∀ x ∈ Set.uIoc a b, |f x - fSeq n x| < 1 := by
    have h := (Metric.tendstoUniformlyOn_iff.mp hlim') 1 (by norm_num)
    refine h.mono ?_
    intro n hn x hx
    have hdist : dist (f x) (fSeq n x) < 1 := hn x hx
    simpa [Real.dist_eq] using hdist
  obtain ⟨N, hN⟩ := (eventually_atTop.1 h_eventually)
  set g : ℝ → ℝ := fun x => |fSeq N x| + 2
  have h_int_abs : IntervalIntegrable (fun x => |fSeq N x|) volume a b := (hint N).abs
  have h_int_const : IntervalIntegrable (fun _x : ℝ => (2 : ℝ)) volume a b := by simp
  have h_int_g : IntervalIntegrable g volume a b := by
    simpa [g] using (IntervalIntegrable.add h_int_abs h_int_const)
  have h_bound_f1 : ∀ x ∈ Set.uIoc a b, |f x| ≤ |fSeq N x| + 1 := by
    intro x hx
    have hdiff : |f x - fSeq N x| < 1 := hN N (le_rfl) x hx
    have htri : |f x| ≤ |fSeq N x| + |f x - fSeq N x| := by
      have h := abs_add_le (fSeq N x) (f x - fSeq N x)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    have hle : |fSeq N x| + |f x - fSeq N x| ≤ |fSeq N x| + 1 :=
      by
        have hle' : |f x - fSeq N x| + |fSeq N x| ≤ 1 + |fSeq N x| :=
          add_le_add_left (le_of_lt hdiff) _
        simpa [add_comm] using hle'
    exact le_trans htri hle
  have h_bound_f : ∀ x ∈ Set.uIoc a b, |f x| ≤ g x := by
    intro x hx
    have hle1 : |f x| ≤ |fSeq N x| + 1 := h_bound_f1 x hx
    have hle2 : |fSeq N x| + 1 ≤ g x := by
      simp [g]
    exact le_trans hle1 hle2
  have h_meas_seq :
      ∀ n, AEStronglyMeasurable (fSeq n) (volume.restrict (Set.uIoc a b)) := by
    intro n
    have h_int : IntegrableOn (fSeq n) (Set.uIoc a b) volume :=
      (intervalIntegrable_iff.mp (hint n))
    exact h_int.aestronglyMeasurable
  have h_lim_ae :
      ∀ᵐ x ∂volume.restrict (Set.uIoc a b),
        Tendsto (fun n => fSeq n x) atTop (𝓝 (f x)) := by
    have h_lim_ae' :
        ∀ᵐ x ∂volume, x ∈ Set.uIoc a b →
          Tendsto (fun n => fSeq n x) atTop (𝓝 (f x)) := by
      refine Filter.Eventually.of_forall ?_
      intro x hx
      exact hlim'.tendsto_at hx
    exact (ae_restrict_iff' (measurableSet_uIoc (a := a) (b := b))).2 h_lim_ae'
  have h_meas_f : AEStronglyMeasurable f (volume.restrict (Set.uIoc a b)) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
        (f := fSeq) (g := f) (μ := volume.restrict (Set.uIoc a b)) ?_ ?_
    · intro n
      exact h_meas_seq n
    · exact h_lim_ae
  have h_int_g' : Integrable g (volume.restrict (Set.uIoc a b)) := by
    simpa [IntegrableOn] using (intervalIntegrable_iff.mp h_int_g)
  have h_bound_f_ae :
      ∀ᵐ x ∂volume.restrict (Set.uIoc a b), ‖f x‖ ≤ g x := by
    have h_bound_f_ae' :
        ∀ᵐ x ∂volume, x ∈ Set.uIoc a b → ‖f x‖ ≤ g x := by
      refine Filter.Eventually.of_forall ?_
      intro x hx
      simpa [Real.norm_eq_abs] using (h_bound_f x hx)
    exact (ae_restrict_iff' (measurableSet_uIoc (a := a) (b := b))).2 h_bound_f_ae'
  have h_int_f : Integrable f (volume.restrict (Set.uIoc a b)) :=
    Integrable.mono' h_int_g' h_meas_f h_bound_f_ae
  have h_int_f_interval : IntervalIntegrable f volume a b := by
    refine intervalIntegrable_iff.mpr ?_
    simpa [IntegrableOn] using h_int_f
  have h_bound_seq :
      ∀ᶠ n in atTop,
        ∀ᵐ x ∂volume, x ∈ Set.uIoc a b → ‖fSeq n x‖ ≤ g x := by
    refine (eventually_atTop.2 ?_)
    refine ⟨N, ?_⟩
    intro n hn
    have h_point : ∀ x ∈ Set.uIoc a b, |fSeq n x| ≤ g x := by
      intro x hx
      have hdiff' : |f x - fSeq n x| < 1 := hN n hn x hx
      have hdiff : |fSeq n x - f x| < 1 := by
        simpa [abs_sub_comm] using hdiff'
      have htri : |fSeq n x| ≤ |f x| + |fSeq n x - f x| := by
        have h := abs_add_le (f x) (fSeq n x - f x)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
      have hle1 : |f x| + |fSeq n x - f x| ≤ |f x| + 1 :=
        by
          have hle' : |fSeq n x - f x| + |f x| ≤ 1 + |f x| :=
            add_le_add_left (le_of_lt hdiff) _
          simpa [add_comm] using hle'
      have hle2 : |f x| + 1 ≤ |fSeq N x| + 2 := by
        nlinarith [h_bound_f1 x hx]
      have hle3 : |fSeq n x| ≤ |fSeq N x| + 2 :=
        le_trans htri (le_trans hle1 hle2)
      simpa [g] using hle3
    refine Filter.Eventually.of_forall ?_
    intro x hx
    simpa [Real.norm_eq_abs] using (h_point x hx)
  have h_lim_ae_global :
      ∀ᵐ x ∂volume, x ∈ Set.uIoc a b →
        Tendsto (fun n => fSeq n x) atTop (𝓝 (f x)) := by
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact hlim'.tendsto_at hx
  have h_tendsto :
      Tendsto (fun n : ℕ => ∫ x in a..b, fSeq n x) atTop
        (𝓝 (∫ x in a..b, f x)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := a) (b := b) (f := f) (F := fSeq) (l := atTop) g ?_ ?_ h_int_g ?_
    · exact Filter.Eventually.of_forall h_meas_seq
    · exact h_bound_seq
    · exact h_lim_ae_global
  exact ⟨h_int_f_interval, h_tendsto⟩

lemma example6_2_5_abs_diff_le (n : ℕ) (x : ℝ) :
    |(((Nat.succ n : ℝ) * x + Real.sin ((Nat.succ n : ℝ) * x ^ 2)) /
        (Nat.succ n : ℝ) - x)|
      ≤ 1 / (Nat.succ n : ℝ) := by
  have hnpos : 0 < (Nat.succ n : ℝ) := by
    exact_mod_cast (Nat.succ_pos n)
  have hnne : (Nat.succ n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  have hdiff :
      (((Nat.succ n : ℝ) * x + Real.sin ((Nat.succ n : ℝ) * x ^ 2)) /
          (Nat.succ n : ℝ) - x)
        = Real.sin ((Nat.succ n : ℝ) * x ^ 2) / (Nat.succ n : ℝ) := by
    field_simp [hnne]
    ring
  have hsinle :
      |Real.sin ((Nat.succ n : ℝ) * x ^ 2)| ≤ (1 : ℝ) := by
    simpa using
      (Real.abs_sin_le_one ((Nat.succ n : ℝ) * x ^ 2))
  have hinv_nonneg : 0 ≤ (Nat.succ n : ℝ)⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt hnpos)
  have hmul :
      |Real.sin ((Nat.succ n : ℝ) * x ^ 2)| * (Nat.succ n : ℝ)⁻¹ ≤
        (1 : ℝ) * (Nat.succ n : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_right hsinle hinv_nonneg
  have hdiv :
      |Real.sin ((Nat.succ n : ℝ) * x ^ 2)| / (Nat.succ n : ℝ) ≤
        1 / (Nat.succ n : ℝ) := by
    simpa [div_eq_mul_inv] using hmul
  calc
    |(((Nat.succ n : ℝ) * x + Real.sin ((Nat.succ n : ℝ) * x ^ 2)) /
          (Nat.succ n : ℝ) - x)|
        = |Real.sin ((Nat.succ n : ℝ) * x ^ 2) / (Nat.succ n : ℝ)| := by
          simpa using congrArg abs hdiff
    _ = |Real.sin ((Nat.succ n : ℝ) * x ^ 2)| / (Nat.succ n : ℝ) := by
          have hnonneg : 0 ≤ (Nat.succ n : ℝ) := le_of_lt hnpos
          rw [abs_div, abs_of_nonneg hnonneg]
    _ ≤ 1 / (Nat.succ n : ℝ) := hdiv

lemma example6_2_5_tendsto_uniformlyOn :
    TendstoUniformlyOn
      (fun n : ℕ => fun x : ℝ =>
        ((Nat.succ n : ℝ) * x + Real.sin ((Nat.succ n : ℝ) * x ^ 2)) /
          (Nat.succ n : ℝ))
      (fun x : ℝ => x) atTop (Set.Icc (0 : ℝ) 1) := by
  refine (Metric.tendstoUniformlyOn_iff).2 ?_
  intro ε hε
  rcases (exists_nat_one_div_lt (K := ℝ) hε) with ⟨N, hN⟩
  refine (eventually_atTop.2 ?_)
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hbound :
      |(((Nat.succ n : ℝ) * x + Real.sin ((Nat.succ n : ℝ) * x ^ 2)) /
          (Nat.succ n : ℝ) - x)|
        ≤ 1 / (Nat.succ n : ℝ) :=
    example6_2_5_abs_diff_le n x
  have hmono : 1 / (Nat.succ n : ℝ) ≤ 1 / (Nat.succ N : ℝ) := by
    have hle : (Nat.succ N : ℝ) ≤ (Nat.succ n : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ hn)
    have hNpos : 0 < (Nat.succ N : ℝ) := by
      exact_mod_cast (Nat.succ_pos N)
    exact one_div_le_one_div_of_le hNpos hle
  have hbound' :
      |(((Nat.succ n : ℝ) * x + Real.sin ((Nat.succ n : ℝ) * x ^ 2)) /
          (Nat.succ n : ℝ) - x)|
        ≤ 1 / (Nat.succ N : ℝ) :=
    le_trans hbound hmono
  have hlt :
      |(((Nat.succ n : ℝ) * x + Real.sin ((Nat.succ n : ℝ) * x ^ 2)) /
          (Nat.succ n : ℝ) - x)| < ε :=
    lt_of_le_of_lt hbound' (by simpa using hN)
  simpa [Real.dist_eq, abs_sub_comm] using hlt

lemma example6_2_5_intervalIntegrable (n : ℕ) :
    IntervalIntegrable
      (fun x : ℝ =>
        ((Nat.succ n : ℝ) * x + Real.sin ((Nat.succ n : ℝ) * x ^ 2)) /
          (Nat.succ n : ℝ))
      volume 0 1 := by
  have hcont : Continuous fun x : ℝ =>
      ((Nat.succ n : ℝ) * x + Real.sin ((Nat.succ n : ℝ) * x ^ 2)) /
        (Nat.succ n : ℝ) := by
    fun_prop
  simpa using (hcont.intervalIntegrable (a := (0 : ℝ)) (b := 1))

lemma example6_2_5_integral_id :
    ∫ x in (0 : ℝ)..1, x = (1 : ℝ) / 2 := by
  simp [integral_id]

/-- Example 6.2.5: For `fₙ(x) = ((n x) + sin (n x²)) / n` on `[0,1]`, the
functions converge uniformly to `x`, so the integrals converge to the
integral of the limit.  Therefore
`lim_{n → ∞} ∫₀¹ ((n x + sin (n x²)) / n) = 1 / 2`. -/
theorem example6_2_5_integral_limit :
    Tendsto (fun n : ℕ =>
      ∫ x in (0)..1,
        ((Nat.succ n : ℝ) * x + Real.sin ((Nat.succ n : ℝ) * x ^ 2))
          / (Nat.succ n : ℝ))
      atTop (𝓝 ((1 : ℝ) / 2)) := by
  have h :=
    integral_interval_tendsto_of_uniform_limit
      (a := (0 : ℝ)) (b := 1) (f := fun x : ℝ => x)
      (fSeq := fun n : ℕ => fun x : ℝ =>
        ((Nat.succ n : ℝ) * x + Real.sin ((Nat.succ n : ℝ) * x ^ 2)) /
          (Nat.succ n : ℝ))
      example6_2_5_intervalIntegrable
      example6_2_5_tendsto_uniformlyOn
      (by norm_num)
  simpa [example6_2_5_integral_id] using h.2

/-- Example 6.2.6: The functions `fₙ : [0, 1] → ℝ` are `1` at rationals
whose reduced denominator is at most `n` and `0` otherwise. Each `fₙ` is
Riemann integrable with integral `0`, the sequence converges pointwise to the
Dirichlet function that is `1` on `ℚ` and `0` on irrationals, and this limit
is not Riemann integrable. -/
def example6_2_6_fn (n : ℕ) (x : ℝ) : ℝ := by
  classical
  exact if h : ∃ q : ℚ, (q : ℝ) = x ∧ q.den ≤ n then 1 else 0

/-- The pointwise limit in Example 6.2.6 is the Dirichlet function, equal to
`1` on rational points and `0` on irrational points. -/
def example6_2_6_limit (x : ℝ) : ℝ := by
  classical
  exact if ∃ q : ℚ, (q : ℝ) = x then 1 else 0

/-- Each function in the sequence from Example 6.2.6 is Riemann integrable on
`[0, 1]` with integral `0`. -/
lemma example6_2_6_fn_riemann_integral (n : ℕ) :
    ∃ hf : RiemannIntegrableOn (example6_2_6_fn n) 0 1,
      riemannIntegral (example6_2_6_fn n) 0 1 hf = 0 := by
  classical
  let S : Set ℝ :=
    {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ q : ℚ, (q : ℝ) = x ∧ q.den ≤ n}
  have hfin : S.Finite := by
    simpa [S] using finite_small_denom_rationals n
  obtain ⟨hf0, hI0⟩ :=
    constant_function_riemannIntegral (c := 0) (a := 0) (b := 1) (by norm_num)
  have hI0' : riemannIntegral (fun _ : ℝ => (0 : ℝ)) 0 1 hf0 = 0 := by
    simpa using hI0
  have hfg :
      ∀ x ∈ Set.Icc (0 : ℝ) 1 \ S,
        example6_2_6_fn n x = (fun _ : ℝ => 0) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := hx.1
    have hxnot : x ∉ S := hx.2
    have hxnot' :
        ¬ (x ∈ Set.Icc (0 : ℝ) 1 ∧
          ∃ q : ℚ, (q : ℝ) = x ∧ q.den ≤ n) := by
      simpa [S] using hxnot
    have hnot : ¬ ∃ q : ℚ, (q : ℝ) = x ∧ q.den ≤ n := by
      intro hq
      exact hxnot' ⟨hxIcc, hq⟩
    simp [example6_2_6_fn, hnot]
  obtain ⟨hf, hI⟩ :=
    riemannIntegral_eq_of_eq_off_finite (a := 0) (b := 1)
      (f := fun _ : ℝ => 0) (g := example6_2_6_fn n) (S := S) hf0 hfin hfg
  refine ⟨hf, ?_⟩
  simpa [hI0'] using hI

/-- The sequence `example6_2_6_fn n` converges pointwise to the Dirichlet
function on `[0, 1]`. -/
lemma example6_2_6_tendsto_dirichlet (x : ℝ) :
    Tendsto (fun n : ℕ => example6_2_6_fn n x) atTop (𝓝 (example6_2_6_limit x)) := by
  classical
  by_cases hrat : ∃ q : ℚ, (q : ℝ) = x
  · have hrat' := hrat
    rcases hrat with ⟨q, hq⟩
    have h_eventually :
        ∀ᶠ n in atTop, example6_2_6_fn n x = 1 := by
      refine (eventually_atTop.2 ?_)
      refine ⟨q.den, ?_⟩
      intro n hn
      have hq' : ∃ q' : ℚ, (q' : ℝ) = x ∧ q'.den ≤ n := by
        exact ⟨q, hq, hn⟩
      simp [example6_2_6_fn, hq']
    refine (tendsto_congr' h_eventually).2 ?_
    simp [example6_2_6_limit, hrat']
  · have h_eventually :
        ∀ᶠ n in atTop, example6_2_6_fn n x = 0 := by
      refine Filter.Eventually.of_forall ?_
      intro n
      have hnot : ¬ ∃ q : ℚ, (q : ℝ) = x ∧ q.den ≤ n := by
        intro hq
        rcases hq with ⟨q, hq⟩
        exact hrat ⟨q, hq.1⟩
      simp [example6_2_6_fn, hnot]
    refine (tendsto_congr' h_eventually).2 ?_
    simp [example6_2_6_limit, hrat]

/-- The Dirichlet function on `[0, 1]` is not Riemann integrable. -/
theorem example6_2_6_dirichlet_not_riemann_integrable :
    ¬ RiemannIntegrableOn example6_2_6_limit 0 1 := by
  classical
  intro hlim
  have hlimit : dirichletFunction = example6_2_6_limit := by
    funext x
    simp [dirichletFunction, realRationals, example6_2_6_limit]
  have hLower : lowerDarbouxIntegral example6_2_6_limit 0 1 = 0 := by
    simpa [hlimit] using dirichletFunction_lower_integral
  have hUpper : upperDarbouxIntegral example6_2_6_limit 0 1 = 1 := by
    simpa [hlimit] using dirichletFunction_upper_integral
  have hcontr : (0 : ℝ) = (1 : ℝ) := by
    calc
      (0 : ℝ) = lowerDarbouxIntegral example6_2_6_limit 0 1 := by
        simpa using hLower.symm
      _ = upperDarbouxIntegral example6_2_6_limit 0 1 := hlim.2
      _ = (1 : ℝ) := hUpper
  exact zero_ne_one hcontr

/-- Example 6.2.7: The functions `fₙ : [0,1] → ℝ` are given by
`fₙ(x) = 0` for `x < 1 / (n + 1)` and `fₙ(x) = 1 / x` otherwise.
Each `fₙ` is bounded on `[0, 1]` by `n + 1`, but the pointwise limit
`f(x) = 0` for `x = 0` and `f(x) = 1 / x` otherwise is unbounded. -/
def example6_2_7_fn (n : ℕ) (x : ℝ) : ℝ :=
  if x < (1 : ℝ) / (Nat.succ n) then 0 else 1 / x

/-- The pointwise limit function in Example 6.2.7, equal to `0` at `0` and
`1 / x` for `x ≠ 0`. -/
def example6_2_7_limit (x : ℝ) : ℝ :=
  if x = 0 then 0 else 1 / x

/-- Each function from Example 6.2.7 is bounded on `[0, 1]` by `n + 1`. -/
lemma example6_2_7_fn_bounded (n : ℕ) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |example6_2_7_fn n x| ≤ (Nat.succ n : ℝ) := by
  intro x hx
  by_cases hxlt : x < (1 : ℝ) / (Nat.succ n)
  · have hxlt' : x < (↑n + 1 : ℝ)⁻¹ := by
      simpa using hxlt
    have hnonneg : (0 : ℝ) ≤ (Nat.succ n : ℝ) := by
      exact_mod_cast (Nat.zero_le (Nat.succ n))
    simpa [example6_2_7_fn, hxlt'] using hnonneg
  · have hxge : (1 : ℝ) / (Nat.succ n) ≤ x := not_lt.mp hxlt
    have hNpos : (0 : ℝ) < (Nat.succ n : ℝ) := by
      exact_mod_cast (Nat.succ_pos n)
    have hpos : (0 : ℝ) < (1 : ℝ) / (Nat.succ n : ℝ) :=
      one_div_pos.mpr hNpos
    have hxpos : 0 < x := lt_of_lt_of_le hpos hxge
    have hdiv :
        1 / x ≤ (1 : ℝ) / ((1 : ℝ) / (Nat.succ n : ℝ)) :=
      one_div_le_one_div_of_le hpos hxge
    have hne : (Nat.succ n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero n)
    have hcalc :
        (1 : ℝ) / ((1 : ℝ) / (Nat.succ n : ℝ)) = (Nat.succ n : ℝ) := by
      field_simp [hne]
    have hdiv' : 1 / x ≤ (Nat.succ n : ℝ) := by
      simpa [hcalc] using hdiv
    have habs : |x|⁻¹ ≤ (Nat.succ n : ℝ) := by
      simpa [abs_of_pos hxpos] using hdiv'
    have hxlt' : ¬ x < (↑n + 1 : ℝ)⁻¹ := by
      simpa using hxlt
    simpa [example6_2_7_fn, hxlt'] using habs

/-- The sequence in Example 6.2.7 converges pointwise on `[0, 1]` to the
function that is `0` at `0` and `1 / x` elsewhere. -/
lemma example6_2_7_tendsto {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => example6_2_7_fn n x) atTop (𝓝 (example6_2_7_limit x)) := by
  by_cases hx0 : x = 0
  · subst hx0
    have h_eq : ∀ n : ℕ, example6_2_7_fn n 0 = (0 : ℝ) := by
      intro n
      simp [example6_2_7_fn]
    refine (tendsto_congr h_eq).2 ?_
    simp [example6_2_7_limit]
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hxpos
    have h_eventually : ∀ᶠ n in atTop, example6_2_7_fn n x = 1 / x := by
      refine (eventually_atTop.2 ?_)
      refine ⟨N, ?_⟩
      intro n hn
      have hpos : (0 : ℝ) < (Nat.succ N : ℝ) := by
        exact_mod_cast (Nat.succ_pos N)
      have hle : (Nat.succ N : ℝ) ≤ (Nat.succ n : ℝ) := by
        exact_mod_cast (Nat.succ_le_succ hn)
      have hdiv : 1 / (Nat.succ n : ℝ) ≤ 1 / (Nat.succ N : ℝ) :=
        one_div_le_one_div_of_le hpos hle
      have hxge : 1 / (Nat.succ n : ℝ) ≤ x := by
        refine le_trans hdiv ?_
        exact le_of_lt (by simpa using hN)
      have hxlt : ¬ x < (1 : ℝ) / (Nat.succ n) := not_lt.mpr hxge
      have hxlt' : ¬ x < (↑n + 1 : ℝ)⁻¹ := by
        simpa using hxlt
      simp [example6_2_7_fn, hxlt']
    refine (tendsto_congr' h_eventually).2 ?_
    simp [example6_2_7_limit, hx0]

/-- The pointwise limit in Example 6.2.7 is unbounded on `[0, 1]`. -/
theorem example6_2_7_limit_unbounded :
    ¬ ∃ C : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, |example6_2_7_limit x| ≤ C := by
  intro hC
  rcases hC with ⟨C, hC⟩
  have hCnonneg : 0 ≤ C := by
    have h0 := hC 0 (by simp)
    simpa [example6_2_7_limit] using h0
  have hCpos : (0 : ℝ) < C + 1 := by linarith
  set x : ℝ := (1 : ℝ) / (C + 1)
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · have hCnonneg' : (0 : ℝ) ≤ C + 1 := by linarith
      exact one_div_nonneg.mpr hCnonneg'
    · have hle : (1 : ℝ) ≤ C + 1 := by linarith
      have hpos : (0 : ℝ) < (1 : ℝ) := by norm_num
      have hdiv : (1 : ℝ) / (C + 1) ≤ (1 : ℝ) / (1 : ℝ) :=
        one_div_le_one_div_of_le hpos hle
      simpa [x] using hdiv
  have hCne : (C + 1 : ℝ) ≠ 0 := by
    exact ne_of_gt hCpos
  have hxne : x ≠ 0 := by
    dsimp [x]
    exact one_div_ne_zero hCne
  have hcalc : (1 : ℝ) / x = C + 1 := by
    dsimp [x]
    field_simp [hCne]
  have habs : |example6_2_7_limit x| = C + 1 := by
    have hxnonneg : (0 : ℝ) ≤ C + 1 := by linarith
    calc
      |example6_2_7_limit x| = |1 / x| := by
        simp [example6_2_7_limit, hxne]
      _ = |C + 1| := by simp [hcalc]
      _ = C + 1 := by simp [abs_of_nonneg hxnonneg]
  have hbound := hC x hxIcc
  have hcontr : (C + 1 : ℝ) ≤ C := by
    simpa [habs] using hbound
  linarith

/-- Example 6.2.8: The functions `fₙ(x) = sin ((n + 1) x) / (n + 1)` converge
uniformly to `0`, whose derivative is `0`.  The derivatives
`fₙ'(x) = cos ((n + 1) x)` do not converge pointwise: at `π` they oscillate
between `1` and `-1`, and at `0` they are constantly `1`, not approaching `0`. -/
def example6_2_8_fn (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin ((Nat.succ n : ℝ) * x) / (Nat.succ n : ℝ)

lemma example6_2_8_abs_le (n : ℕ) (x : ℝ) :
    |example6_2_8_fn n x| ≤ 1 / (Nat.succ n : ℝ) := by
  have hnpos : 0 < (Nat.succ n : ℝ) := by
    exact_mod_cast (Nat.succ_pos n)
  have hsinle :
      |Real.sin ((Nat.succ n : ℝ) * x)| ≤ (1 : ℝ) := by
    simpa using (Real.abs_sin_le_one ((Nat.succ n : ℝ) * x))
  have hinv_nonneg : 0 ≤ (Nat.succ n : ℝ)⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt hnpos)
  have hmul :
      |Real.sin ((Nat.succ n : ℝ) * x)| * (Nat.succ n : ℝ)⁻¹ ≤
        (1 : ℝ) * (Nat.succ n : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_right hsinle hinv_nonneg
  have hdiv :
      |Real.sin ((Nat.succ n : ℝ) * x)| / (Nat.succ n : ℝ) ≤
        1 / (Nat.succ n : ℝ) := by
    simpa [div_eq_mul_inv] using hmul
  calc
    |example6_2_8_fn n x|
        = |Real.sin ((Nat.succ n : ℝ) * x) / (Nat.succ n : ℝ)| := by
          simp [example6_2_8_fn]
    _ = |Real.sin ((Nat.succ n : ℝ) * x)| / (Nat.succ n : ℝ) := by
          have hnonneg : 0 ≤ (Nat.succ n : ℝ) := le_of_lt hnpos
          rw [abs_div, abs_of_nonneg hnonneg]
    _ ≤ 1 / (Nat.succ n : ℝ) := hdiv

/-- The sequence from Example 6.2.8 converges uniformly to the zero function. -/
lemma example6_2_8_uniform_tendsto_zero :
    TendstoUniformly (fun n : ℕ => fun x : ℝ => example6_2_8_fn n x)
      (fun _ : ℝ => 0) atTop := by
  refine (Metric.tendstoUniformly_iff).2 ?_
  intro ε hε
  rcases (exists_nat_one_div_lt (K := ℝ) hε) with ⟨N, hN⟩
  refine (eventually_atTop.2 ?_)
  refine ⟨N, ?_⟩
  intro n hn x
  have hbound : |example6_2_8_fn n x| ≤ 1 / (Nat.succ n : ℝ) :=
    example6_2_8_abs_le n x
  have hmono : 1 / (Nat.succ n : ℝ) ≤ 1 / (Nat.succ N : ℝ) := by
    have hle : (Nat.succ N : ℝ) ≤ (Nat.succ n : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ hn)
    have hNpos : 0 < (Nat.succ N : ℝ) := by
      exact_mod_cast (Nat.succ_pos N)
    exact one_div_le_one_div_of_le hNpos hle
  have hbound' :
      |example6_2_8_fn n x| ≤ 1 / (Nat.succ N : ℝ) :=
    le_trans hbound hmono
  have hlt : |example6_2_8_fn n x| < ε :=
    lt_of_le_of_lt hbound' (by simpa using hN)
  simpa [Real.dist_eq] using hlt

/-- The derivative of the uniform limit in Example 6.2.8 is identically zero. -/
lemma example6_2_8_deriv_limit (x : ℝ) :
    deriv (fun _ : ℝ => (0 : ℝ)) x = 0 := by
  simp

/-- Each function in Example 6.2.8 has derivative `cos ((n + 1) x)`. -/
lemma example6_2_8_deriv (n : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => example6_2_8_fn n y) x =
      Real.cos ((Nat.succ n : ℝ) * x) := by
  have h_inner :
      HasDerivAt (fun y : ℝ => (Nat.succ n : ℝ) * y) (Nat.succ n : ℝ) x := by
    simpa using (hasDerivAt_const_mul (x := x) (c := (Nat.succ n : ℝ)))
  have h_sin :
      HasDerivAt (fun y : ℝ => Real.sin ((Nat.succ n : ℝ) * y))
        (Real.cos ((Nat.succ n : ℝ) * x) * (Nat.succ n : ℝ)) x := by
    have h := (Real.hasDerivAt_sin ((Nat.succ n : ℝ) * x)).comp x h_inner
    simpa [Function.comp] using h
  have h_mul :
      HasDerivAt
        (fun y : ℝ => Real.sin ((Nat.succ n : ℝ) * y) * (Nat.succ n : ℝ)⁻¹)
        ((Real.cos ((Nat.succ n : ℝ) * x) * (Nat.succ n : ℝ)) *
          (Nat.succ n : ℝ)⁻¹) x := by
    simpa using h_sin.mul_const (Nat.succ n : ℝ)⁻¹
  have hne : (Nat.succ n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  calc
    deriv (fun y : ℝ => example6_2_8_fn n y) x
        = deriv (fun y : ℝ =>
            Real.sin ((Nat.succ n : ℝ) * y) * (Nat.succ n : ℝ)⁻¹) x := by
          simp [example6_2_8_fn, div_eq_mul_inv]
    _ = (Real.cos ((Nat.succ n : ℝ) * x) * (Nat.succ n : ℝ)) *
          (Nat.succ n : ℝ)⁻¹ := h_mul.deriv
    _ = Real.cos ((Nat.succ n : ℝ) * x) := by
          simpa [mul_assoc] using
            (mul_inv_cancel_right₀ hne (Real.cos ((Nat.succ n : ℝ) * x)))

/-- At `π`, the derivatives in Example 6.2.8 oscillate and do not converge. -/
lemma example6_2_8_deriv_not_tendsto_at_pi :
    ¬ Tendsto (fun n : ℕ => deriv (fun y : ℝ => example6_2_8_fn n y) Real.pi)
      atTop (𝓝 0) := by
  intro h
  have hdist :
      Tendsto
        (fun n : ℕ =>
          dist (deriv (fun y : ℝ => example6_2_8_fn n y) Real.pi) 0)
        atTop (𝓝 0) :=
    (tendsto_iff_dist_tendsto_zero).1 h
  have hdist_eq :
      (fun n : ℕ =>
        dist (deriv (fun y : ℝ => example6_2_8_fn n y) Real.pi) 0) =
        (fun _ : ℕ => (1 : ℝ)) := by
    funext n
    have hcos :
        deriv (fun y : ℝ => example6_2_8_fn n y) Real.pi = (-1) ^ (Nat.succ n) := by
      calc
        deriv (fun y : ℝ => example6_2_8_fn n y) Real.pi
            = Real.cos ((Nat.succ n : ℝ) * Real.pi) := example6_2_8_deriv n Real.pi
        _ = (-1) ^ (Nat.succ n) := by
            simpa using (Real.cos_nat_mul_pi (Nat.succ n))
    calc
      dist (deriv (fun y : ℝ => example6_2_8_fn n y) Real.pi) 0
          = |deriv (fun y : ℝ => example6_2_8_fn n y) Real.pi| := by
              simp
      _ = |(-1) ^ (Nat.succ n)| := by
              simp [hcos]
      _ = (1 : ℝ) := by
              simp
  have hdist_eq' :
      ∀ n : ℕ, dist (deriv (fun y : ℝ => example6_2_8_fn n y) Real.pi) 0 = (1 : ℝ) := by
    intro n
    have h := congrArg (fun f => f n) hdist_eq
    simpa using h
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    exact (tendsto_congr hdist_eq').1 hdist
  have hfalse : (1 : ℝ) = (0 : ℝ) := (tendsto_const_nhds_iff).1 hconst
  exact one_ne_zero hfalse

/-- At `0`, the derivatives in Example 6.2.8 are constantly `1`, so the sequence
does not approach `0`. -/
lemma example6_2_8_deriv_at_zero :
    Tendsto (fun n : ℕ => deriv (fun y : ℝ => example6_2_8_fn n y) 0) atTop (𝓝 1) := by
  have h_eq : ∀ n : ℕ, deriv (fun y : ℝ => example6_2_8_fn n y) 0 = (1 : ℝ) := by
    intro n
    calc
      deriv (fun y : ℝ => example6_2_8_fn n y) 0
          = Real.cos ((Nat.succ n : ℝ) * 0) := example6_2_8_deriv n 0
      _ = (1 : ℝ) := by simp
  refine (tendsto_congr h_eq).2 ?_
  simp

/-- Example 6.2.9: Let `fₙ(x) = 1 / (1 + n x²)`. For `x ≠ 0`, `fₙ(x)` converges
to `0`, while `fₙ(0)` converges to `1`, so the pointwise limit is not
continuous at `0`. The derivatives are `fₙ'(x) = - 2 n x / (1 + n x²)²`, which
converge pointwise to `0` but not uniformly on any interval containing `0`.
The limit function fails to be differentiable at `0`. -/
def example6_2_9_fn (n : ℕ) (x : ℝ) : ℝ :=
  1 / (1 + (Nat.succ n : ℝ) * x ^ 2)

/-- Pointwise limit function in Example 6.2.9, equal to `1` at `0` and `0`
elsewhere. -/
def example6_2_9_limit (x : ℝ) : ℝ :=
  if x = 0 then 1 else 0

/-- For `x ≠ 0`, `example6_2_9_fn n x` converges to `0` as `n → ∞`. -/
lemma example6_2_9_tendsto_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => example6_2_9_fn n x) atTop (𝓝 0) := by
  have hx2pos : 0 < x ^ 2 := by
    simpa using (sq_pos_of_ne_zero (a := x) hx)
  have h_div :
      Tendsto (fun n : ℕ => (1 : ℝ) / (Nat.succ n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h_mul :
      Tendsto (fun n : ℕ => (1 / x ^ 2) * (1 / (Nat.succ n : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    have hconst : Tendsto (fun _ : ℕ => (1 / x ^ 2)) atTop (𝓝 (1 / x ^ 2)) :=
      tendsto_const_nhds
    have h := hconst.mul h_div
    simpa using h
  have hnonneg : ∀ n, 0 ≤ example6_2_9_fn n x := by
    intro n
    have hx2nonneg : 0 ≤ x ^ 2 := by
      exact sq_nonneg x
    have hpos_n : 0 ≤ (Nat.succ n : ℝ) := by
      exact_mod_cast (Nat.succ_pos n).le
    have hnonneg' : 0 ≤ 1 + (Nat.succ n : ℝ) * x ^ 2 := by
      have hmul : 0 ≤ (Nat.succ n : ℝ) * x ^ 2 := by
        exact mul_nonneg hpos_n hx2nonneg
      linarith
    simpa [example6_2_9_fn] using (one_div_nonneg.mpr hnonneg')
  have hle : ∀ n, example6_2_9_fn n x ≤ (1 / x ^ 2) * (1 / (Nat.succ n : ℝ)) := by
    intro n
    have hx2pos' : 0 < x ^ 2 := hx2pos
    have hpos_n : 0 < (Nat.succ n : ℝ) := by
      exact_mod_cast (Nat.succ_pos n)
    have hpos_mul : 0 < (Nat.succ n : ℝ) * x ^ 2 := by
      exact mul_pos hpos_n hx2pos'
    have hle' :
        (Nat.succ n : ℝ) * x ^ 2 ≤ 1 + (Nat.succ n : ℝ) * x ^ 2 := by linarith
    have hdiv_le :
        1 / (1 + (Nat.succ n : ℝ) * x ^ 2) ≤ 1 / ((Nat.succ n : ℝ) * x ^ 2) :=
      one_div_le_one_div_of_le hpos_mul hle'
    have hrewrite :
        1 / ((Nat.succ n : ℝ) * x ^ 2) =
          (1 / (Nat.succ n : ℝ)) * (1 / x ^ 2) := by
      symm
      simpa using (one_div_mul_one_div (a := (Nat.succ n : ℝ)) (b := x ^ 2))
    calc
      example6_2_9_fn n x
          = 1 / (1 + (Nat.succ n : ℝ) * x ^ 2) := by rfl
      _ ≤ 1 / ((Nat.succ n : ℝ) * x ^ 2) := hdiv_le
      _ = (1 / (Nat.succ n : ℝ)) * (1 / x ^ 2) := hrewrite
      _ = (1 / x ^ 2) * (1 / (Nat.succ n : ℝ)) := by
          simp [mul_comm]
  have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h0 h_mul ?_ ?_
  · intro n
    exact hnonneg n
  · intro n
    exact hle n

/-- At `x = 0`, the sequence `example6_2_9_fn n 0` converges to `1`. -/
lemma example6_2_9_tendsto_zero :
    Tendsto (fun n : ℕ => example6_2_9_fn n 0) atTop (𝓝 1) := by
  have h_eq : ∀ n : ℕ, example6_2_9_fn n 0 = (1 : ℝ) := by
    intro n
    simp [example6_2_9_fn]
  refine (tendsto_congr h_eq).2 ?_
  simp

/-- The pointwise limit of Example 6.2.9 is not continuous at `0`. -/
theorem example6_2_9_limit_not_continuous :
    ¬ ContinuousAt example6_2_9_limit 0 := by
  intro hcont
  have hseq :
      Tendsto (fun n : ℕ => (1 : ℝ) / (Nat.succ n)) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim :
      Tendsto (fun n : ℕ => example6_2_9_limit ((1 : ℝ) / (Nat.succ n)))
        atTop (𝓝 (example6_2_9_limit 0)) :=
    hcont.tendsto.comp hseq
  have hlim0 :
      Tendsto (fun n : ℕ => example6_2_9_limit ((1 : ℝ) / (Nat.succ n)))
        atTop (𝓝 (0 : ℝ)) := by
    have h_eq :
        ∀ n : ℕ, example6_2_9_limit ((1 : ℝ) / (Nat.succ n)) = (0 : ℝ) := by
      intro n
      have hne' : (Nat.succ n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero n)
      have hne : (1 : ℝ) / (Nat.succ n : ℝ) ≠ 0 := by
        exact one_div_ne_zero hne'
      unfold example6_2_9_limit
      exact if_neg hne
    refine (tendsto_congr h_eq).2 ?_
    simp
  have h_eq : example6_2_9_limit 0 = (0 : ℝ) :=
    tendsto_nhds_unique hlim hlim0
  simp [example6_2_9_limit] at h_eq

/-- Derivative formula for the functions in Example 6.2.9. -/
lemma example6_2_9_deriv (n : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => example6_2_9_fn n y) x =
      (-2 * (Nat.succ n : ℝ) * x) / (1 + (Nat.succ n : ℝ) * x ^ 2) ^ 2 := by
  have h_pow :
      HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow (n := 2) (x := x))
  have h_mul :
      HasDerivAt (fun y : ℝ => (Nat.succ n : ℝ) * y ^ 2)
        ((Nat.succ n : ℝ) * (2 * x)) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_pow.const_mul (Nat.succ n : ℝ)
  have h_add :
      HasDerivAt (fun y : ℝ => 1 + (Nat.succ n : ℝ) * y ^ 2)
        ((Nat.succ n : ℝ) * (2 * x)) x := by
    simpa using h_mul.const_add (1 : ℝ)
  have hne : (1 + (Nat.succ n : ℝ) * x ^ 2) ≠ 0 := by
    have hx2nonneg : 0 ≤ x ^ 2 := by exact sq_nonneg x
    have hpos_n : 0 ≤ (Nat.succ n : ℝ) := by
      exact_mod_cast (Nat.succ_pos n).le
    have hpos : 0 < 1 + (Nat.succ n : ℝ) * x ^ 2 := by
      have hmul : 0 ≤ (Nat.succ n : ℝ) * x ^ 2 := by
        exact mul_nonneg hpos_n hx2nonneg
      linarith
    exact ne_of_gt hpos
  have h_inv :
      HasDerivAt (fun y : ℝ => (1 + (Nat.succ n : ℝ) * y ^ 2)⁻¹)
        (-((Nat.succ n : ℝ) * (2 * x)) / (1 + (Nat.succ n : ℝ) * x ^ 2) ^ 2) x := by
    simpa using (h_add.fun_inv hne)
  calc
    deriv (fun y : ℝ => example6_2_9_fn n y) x
        = deriv (fun y : ℝ => (1 + (Nat.succ n : ℝ) * y ^ 2)⁻¹) x := by
          simp [example6_2_9_fn, one_div]
    _ = -((Nat.succ n : ℝ) * (2 * x)) / (1 + (Nat.succ n : ℝ) * x ^ 2) ^ 2 := h_inv.deriv
    _ = (-2 * (Nat.succ n : ℝ) * x) / (1 + (Nat.succ n : ℝ) * x ^ 2) ^ 2 := by
          have hnum : -((↑n + 1 : ℝ) * (2 * x)) = -(2 * (↑n + 1 : ℝ) * x) := by
            ring
          simp [hnum]

/-- For every `x`, the derivatives in Example 6.2.9 converge pointwise to `0`. -/
lemma example6_2_9_deriv_tendsto_zero (x : ℝ) :
    Tendsto (fun n : ℕ => deriv (fun y : ℝ => example6_2_9_fn n y) x) atTop (𝓝 0) := by
  by_cases hx : x = 0
  · subst hx
    have h_eq : ∀ n, deriv (fun y : ℝ => example6_2_9_fn n y) 0 = 0 := by
      intro n
      simp [example6_2_9_deriv]
    refine (tendsto_congr h_eq).2 ?_
    simp
  · have hx2pos : 0 < x ^ 2 := by
      simpa using (sq_pos_of_ne_zero (a := x) hx)
    set C : ℝ := (2 * |x|) / (x ^ 2) ^ 2
    have h_div :
        Tendsto (fun n : ℕ => (1 : ℝ) / (Nat.succ n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hC :
        Tendsto (fun n : ℕ => C * (1 / (Nat.succ n : ℝ))) atTop (𝓝 (0 : ℝ)) := by
      have hconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
      have h := hconst.mul h_div
      simpa using h
    have hbound :
        ∀ n, dist (deriv (fun y : ℝ => example6_2_9_fn n y) x) 0
          ≤ C * (1 / (Nat.succ n : ℝ)) := by
      intro n
      have hA_pos : 0 < (Nat.succ n : ℝ) := by
        exact_mod_cast (Nat.succ_pos n)
      have hA_nonneg : 0 ≤ (Nat.succ n : ℝ) := le_of_lt hA_pos
      have hpos_den : 0 < (1 + (Nat.succ n : ℝ) * x ^ 2) := by
        have hmul : 0 ≤ (Nat.succ n : ℝ) * x ^ 2 := by
          exact mul_nonneg hA_nonneg (sq_nonneg x)
        linarith
      have hpos_den_sq : 0 < (1 + (Nat.succ n : ℝ) * x ^ 2) ^ 2 := by
        exact pow_pos hpos_den 2
      have habs_num :
          |(-2 * (Nat.succ n : ℝ) * x)| = 2 * (Nat.succ n : ℝ) * |x| := by
        calc
          |(-2 * (Nat.succ n : ℝ) * x)| = |(-2)| * |(Nat.succ n : ℝ)| * |x| := by
            simp [abs_mul, mul_assoc]
          _ = 2 * (Nat.succ n : ℝ) * |x| := by
            have h1 : |(-2 : ℝ)| = (2 : ℝ) := by simp
            have h2 : |(Nat.succ n : ℝ)| = (Nat.succ n : ℝ) := by
              exact abs_of_nonneg hA_nonneg
            rw [h1, h2]
      have hdist :
          dist (deriv (fun y : ℝ => example6_2_9_fn n y) x) 0
            = (2 * (Nat.succ n : ℝ) * |x|) /
              (1 + (Nat.succ n : ℝ) * x ^ 2) ^ 2 := by
        calc
          dist (deriv (fun y : ℝ => example6_2_9_fn n y) x) 0
              = |deriv (fun y : ℝ => example6_2_9_fn n y) x| := by
                  simp
          _ = |(-2 * (Nat.succ n : ℝ) * x) /
              (1 + (Nat.succ n : ℝ) * x ^ 2) ^ 2| := by
                  simp [example6_2_9_deriv]
          _ = |(-2 * (Nat.succ n : ℝ) * x)| /
              (1 + (Nat.succ n : ℝ) * x ^ 2) ^ 2 := by
                  simp [abs_div]
          _ = (2 * (Nat.succ n : ℝ) * |x|) /
              (1 + (Nat.succ n : ℝ) * x ^ 2) ^ 2 := by
                  rw [habs_num]
      have hle_sq :
          ((Nat.succ n : ℝ) * x ^ 2) ^ 2 ≤
            (1 + (Nat.succ n : ℝ) * x ^ 2) ^ 2 := by
        have hle :
            (Nat.succ n : ℝ) * x ^ 2 ≤
              1 + (Nat.succ n : ℝ) * x ^ 2 := by linarith
        have hnonneg : 0 ≤ (Nat.succ n : ℝ) * x ^ 2 := by
          exact mul_nonneg hA_nonneg (sq_nonneg x)
        have h := mul_le_mul hle hle hnonneg (by linarith)
        simpa [pow_two] using h
      have hnum_nonneg : 0 ≤ 2 * (Nat.succ n : ℝ) * |x| := by
        have hxabs : 0 ≤ |x| := abs_nonneg x
        nlinarith [hA_nonneg, hxabs]
      have hpos_sq : 0 < ((Nat.succ n : ℝ) * x ^ 2) ^ 2 := by
        have hpos_mul : 0 < (Nat.succ n : ℝ) * x ^ 2 := by
          exact mul_pos hA_pos hx2pos
        exact pow_pos hpos_mul 2
      have hdiv_le :
          (2 * (Nat.succ n : ℝ) * |x|) /
              (1 + (Nat.succ n : ℝ) * x ^ 2) ^ 2
            ≤ (2 * (Nat.succ n : ℝ) * |x|) /
              ((Nat.succ n : ℝ) * x ^ 2) ^ 2 := by
        exact div_le_div_of_nonneg_left hnum_nonneg hpos_sq hle_sq
      have hrewrite :
          (2 * (Nat.succ n : ℝ) * |x|) /
              ((Nat.succ n : ℝ) * x ^ 2) ^ 2
            = C * (1 / (Nat.succ n : ℝ)) := by
        have hA_ne : (Nat.succ n : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.succ_ne_zero n)
        have hx2_ne : x ^ 2 ≠ 0 := by
          exact pow_ne_zero 2 hx
        simp [C]
        field_simp [hA_ne, hx2_ne, pow_two, mul_comm, mul_left_comm, mul_assoc]
      calc
        dist (deriv (fun y : ℝ => example6_2_9_fn n y) x) 0
            = (2 * (Nat.succ n : ℝ) * |x|) /
              (1 + (Nat.succ n : ℝ) * x ^ 2) ^ 2 := hdist
        _ ≤ (2 * (Nat.succ n : ℝ) * |x|) /
              ((Nat.succ n : ℝ) * x ^ 2) ^ 2 := hdiv_le
        _ = C * (1 / (Nat.succ n : ℝ)) := hrewrite
    have hdist :
        Tendsto (fun n : ℕ => dist (deriv (fun y : ℝ => example6_2_9_fn n y) x) 0)
          atTop (𝓝 (0 : ℝ)) := by
      refine squeeze_zero ?_ ?_ hC
      · intro n; exact dist_nonneg
      · intro n; exact hbound n
    exact (tendsto_iff_dist_tendsto_zero).2 hdist

/-- The derivatives from Example 6.2.9 do not converge uniformly on any
interval containing `0`. -/
lemma example6_2_9_deriv_not_uniform :
    ¬ ∃ a b : ℝ, a < 0 ∧ 0 < b ∧
        TendstoUniformlyOn (fun n : ℕ => fun x : ℝ => deriv (fun y : ℝ => example6_2_9_fn n y) x)
          (fun _ : ℝ => 0) atTop (Set.Icc a b) := by
  intro h
  rcases h with ⟨a, b, ha, hb, huni⟩
  have huni' := (Metric.tendstoUniformlyOn_iff.mp huni) (1 / 2) (by norm_num)
  rcases (eventually_atTop.1 huni') with ⟨N, hN⟩
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt hb
  let n : ℕ := max N K
  have hnN : N ≤ n := le_max_left _ _
  have hnK : K ≤ n := le_max_right _ _
  have hxpos : 0 < (1 : ℝ) / (Nat.succ n : ℝ) := by
    have hpos : 0 < (Nat.succ n : ℝ) := by
      exact_mod_cast (Nat.succ_pos n)
    exact one_div_pos.mpr hpos
  have hxleft : a ≤ (1 : ℝ) / (Nat.succ n : ℝ) := by
    have hnonneg : 0 ≤ (1 : ℝ) / (Nat.succ n : ℝ) := le_of_lt hxpos
    exact le_trans (le_of_lt ha) hnonneg
  have hxright : (1 : ℝ) / (Nat.succ n : ℝ) ≤ b := by
    have hposK : 0 < (Nat.succ K : ℝ) := by
      exact_mod_cast (Nat.succ_pos K)
    have hle : (Nat.succ K : ℝ) ≤ (Nat.succ n : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ hnK)
    have hdiv :
        (1 : ℝ) / (Nat.succ n : ℝ) ≤ (1 : ℝ) / (Nat.succ K : ℝ) :=
      one_div_le_one_div_of_le hposK hle
    have hK' : (1 : ℝ) / (Nat.succ K : ℝ) < b := by
      simpa using hK
    exact le_trans hdiv (le_of_lt hK')
  have hxmem : (1 : ℝ) / (Nat.succ n : ℝ) ∈ Set.Icc a b := ⟨hxleft, hxright⟩
  have hlt :
      dist (deriv (fun y : ℝ => example6_2_9_fn n y) ((1 : ℝ) / (Nat.succ n : ℝ))) 0
        < (1 / 2 : ℝ) := by
    have hlt' := hN n hnN _ hxmem
    simpa [dist_comm] using hlt'
  have hdist_eq :
      dist (deriv (fun y : ℝ => example6_2_9_fn n y) ((1 : ℝ) / (Nat.succ n : ℝ))) 0
        = (2 : ℝ) / (1 + (1 : ℝ) / (Nat.succ n : ℝ)) ^ 2 := by
    have hpos : 0 < (1 + (1 : ℝ) / (Nat.succ n : ℝ)) ^ 2 := by
      have hpos' : 0 < (1 : ℝ) / (Nat.succ n : ℝ) := by
        have hposn : 0 < (Nat.succ n : ℝ) := by
          exact_mod_cast (Nat.succ_pos n)
        exact one_div_pos.mpr hposn
      have hpos'' : 0 < 1 + (1 : ℝ) / (Nat.succ n : ℝ) := by linarith
      exact pow_pos hpos'' 2
    have hderiv_eq :
        |deriv (fun y : ℝ => example6_2_9_fn n y) ((1 : ℝ) / (Nat.succ n : ℝ))|
          = |(-2 * (Nat.succ n : ℝ) * ((1 : ℝ) / (Nat.succ n : ℝ))) /
              (1 + (Nat.succ n : ℝ) * ((1 : ℝ) / (Nat.succ n : ℝ)) ^ 2) ^ 2| := by
      simpa using
        congrArg abs (example6_2_9_deriv n ((1 : ℝ) / (Nat.succ n : ℝ)))
    calc
      dist (deriv (fun y : ℝ => example6_2_9_fn n y) ((1 : ℝ) / (Nat.succ n : ℝ))) 0
          = |deriv (fun y : ℝ => example6_2_9_fn n y) ((1 : ℝ) / (Nat.succ n : ℝ))| := by
              simp
      _ = |(-2 * (Nat.succ n : ℝ) * ((1 : ℝ) / (Nat.succ n : ℝ))) /
            (1 + (Nat.succ n : ℝ) * ((1 : ℝ) / (Nat.succ n : ℝ)) ^ 2) ^ 2| := hderiv_eq
      _ = |(-2 : ℝ) / (1 + (1 : ℝ) / (Nat.succ n : ℝ)) ^ 2| := by
              have hne : (Nat.succ n : ℝ) ≠ 0 := by
                exact_mod_cast (Nat.succ_ne_zero n)
              have hcalc :
                  (-2 * (Nat.succ n : ℝ) * ((1 : ℝ) / (Nat.succ n : ℝ))) /
                      (1 + (Nat.succ n : ℝ) * ((1 : ℝ) / (Nat.succ n : ℝ)) ^ 2) ^ 2
                    = (-2 : ℝ) / (1 + (1 : ℝ) / (Nat.succ n : ℝ)) ^ 2 := by
                field_simp [hne, pow_two, mul_comm, mul_left_comm, mul_assoc]
              rw [hcalc]
      _ = (2 : ℝ) / (1 + (1 : ℝ) / (Nat.succ n : ℝ)) ^ 2 := by
              simp [abs_div]
  have hge :
      (1 / 2 : ℝ) ≤
        dist (deriv (fun y : ℝ => example6_2_9_fn n y) ((1 : ℝ) / (Nat.succ n : ℝ))) 0 := by
    have hrecip :
        (1 : ℝ) / 4 ≤ 1 / (1 + (1 : ℝ) / (Nat.succ n : ℝ)) ^ 2 := by
      have hle : (1 : ℝ) / (Nat.succ n : ℝ) ≤ (1 : ℝ) := by
        have hle' : (1 : ℝ) ≤ (Nat.succ n : ℝ) := by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
        have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hle'
        simpa using h
      have hsum : 1 + (1 : ℝ) / (Nat.succ n : ℝ) ≤ (2 : ℝ) := by linarith
      have hsum_nonneg : 0 ≤ 1 + (1 : ℝ) / (Nat.succ n : ℝ) := by
        have hpos' : 0 < (1 : ℝ) / (Nat.succ n : ℝ) := by
          have hposn : 0 < (Nat.succ n : ℝ) := by
            exact_mod_cast (Nat.succ_pos n)
          exact one_div_pos.mpr hposn
        linarith
      have hsq_le :
          (1 + (1 : ℝ) / (Nat.succ n : ℝ)) ^ 2 ≤ 4 := by
        have h := mul_le_mul hsum hsum hsum_nonneg (by linarith)
        nlinarith
      have hpos : 0 < (1 + (1 : ℝ) / (Nat.succ n : ℝ)) ^ 2 := by
        have hpos' : 0 < (1 : ℝ) / (Nat.succ n : ℝ) := by
          have hposn : 0 < (Nat.succ n : ℝ) := by
            exact_mod_cast (Nat.succ_pos n)
          exact one_div_pos.mpr hposn
        have hpos'' : 0 < 1 + (1 : ℝ) / (Nat.succ n : ℝ) := by linarith
        exact pow_pos hpos'' 2
      have h := one_div_le_one_div_of_le hpos hsq_le
      simpa using h
    have hmul := mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 2)
    have hge' :
        (1 / 2 : ℝ) ≤ 2 / (1 + (1 : ℝ) / (Nat.succ n : ℝ)) ^ 2 := by
      have hge'' :
          (1 / 2 : ℝ) ≤ 2 * (1 / (1 + (1 : ℝ) / (Nat.succ n : ℝ)) ^ 2) := by
        nlinarith [hmul]
      simpa [mul_comm, mul_left_comm, mul_assoc, one_div, div_eq_mul_inv] using hge''
    rw [hdist_eq]
    exact hge'
  exact (not_lt_of_ge hge) hlt

/-- The pointwise limit in Example 6.2.9 is not differentiable at `0`. -/
theorem example6_2_9_limit_not_differentiable :
    ¬ DifferentiableAt ℝ example6_2_9_limit 0 := by
  intro hdiff
  exact example6_2_9_limit_not_continuous hdiff.continuousAt

/-- Theorem 6.2.10: Let `I` be a bounded interval and let `fₙ : I → ℝ` be
continuously differentiable functions. If the derivatives `fₙ'` converge
uniformly on `I` to `g` and the sequence of values `fₙ(c)` converges for some
`c ∈ I`, then `fₙ` converges uniformly on `I` to a continuously differentiable
function `f` with derivative `f' = g`. -/
theorem uniform_limit_of_uniform_deriv
    {a b : ℝ} (fSeq : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (c : ℝ)
    (hcont : ∀ n, ContDiffOn ℝ 1 (fSeq n) (Set.Icc a b))
    (hderiv : TendstoUniformlyOn
      (fun n x => derivWithin (fSeq n) (Set.Icc a b) x) g atTop (Set.Icc a b))
    (hc : c ∈ Set.Icc a b) (hval : ∃ l, Tendsto (fun n => fSeq n c) atTop (𝓝 l)) :
    ∃ f : ℝ → ℝ,
      ContDiffOn ℝ 1 f (Set.Icc a b) ∧
        TendstoUniformlyOn fSeq f atTop (Set.Icc a b) ∧
          ∀ x ∈ Set.Icc a b, derivWithin f (Set.Icc a b) x = g x := by
  classical
  obtain ⟨l, hl⟩ := hval
  have hab : a ≤ b := le_trans hc.1 hc.2
  by_cases hlt : a < b
  · have h_unique : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hlt
    have hderiv_cont :
        ∀ n, Continuous (fun x : {x // x ∈ Set.Icc a b} =>
          derivWithin (fSeq n) (Set.Icc a b) x) := by
      intro n
      have hcontOn :
          ContinuousOn (fun x => derivWithin (fSeq n) (Set.Icc a b) x) (Set.Icc a b) :=
        (hcont n).continuousOn_derivWithin h_unique (by simp)
      simpa using hcontOn.restrict
    have hderiv_restrict :
        TendstoUniformly (fun n (x : {x // x ∈ Set.Icc a b}) =>
          derivWithin (fSeq n) (Set.Icc a b) x) (fun x => g x) atTop := by
      simpa [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe] using hderiv
    have hcont_g_subtype :
        Continuous (fun x : {x // x ∈ Set.Icc a b} => g x) :=
      continuous_of_uniformLimit (S := Set.Icc a b)
        (fSeq := fun n x => derivWithin (fSeq n) (Set.Icc a b) x)
        (f := fun x => g x) hderiv_cont hderiv_restrict
    have hcont_g : ContinuousOn g (Set.Icc a b) := by
      simpa [continuousOn_iff_continuous_restrict] using hcont_g_subtype
    let f : ℝ → ℝ := fun x => l + ∫ t in c..x, g t
    have hf_hasDeriv :
        ∀ x ∈ Set.Icc a b, HasDerivWithinAt f (g x) (Set.Icc a b) x := by
      intro x hx
      have hsubset : Set.uIcc c x ⊆ Set.Icc a b := by
        intro t ht
        have hmin : a ≤ min c x := le_min hc.1 hx.1
        have hmax : max c x ≤ b := max_le hc.2 hx.2
        exact ⟨le_trans hmin ht.1, le_trans ht.2 hmax⟩
      have hcont_uIcc : ContinuousOn g (Set.uIcc c x) := hcont_g.mono hsubset
      have hInt : IntervalIntegrable g volume c x :=
        hcont_uIcc.intervalIntegrable (μ := volume)
      have hmeas :
          StronglyMeasurableAtFilter g (𝓝[Set.Icc a b] x) volume :=
        hcont_g.stronglyMeasurableAtFilter_nhdsWithin (μ := volume) measurableSet_Icc x
      have hcontWithin : ContinuousWithinAt g (Set.Icc a b) x :=
        hcont_g.continuousWithinAt hx
      haveI : Fact (x ∈ Set.Icc a b) := ⟨hx⟩
      have hderiv_int :
          HasDerivWithinAt (fun u => ∫ t in c..u, g t) (g x) (Set.Icc a b) x :=
        intervalIntegral.integral_hasDerivWithinAt_right (a := c) (b := x) (f := g)
          hInt (s := Set.Icc a b) (t := Set.Icc a b) hmeas hcontWithin
      simpa [f] using hderiv_int.const_add l
    have hf_deriv : ∀ x ∈ Set.Icc a b, derivWithin f (Set.Icc a b) x = g x := by
      intro x hx
      exact (hf_hasDeriv x hx).derivWithin (h_unique.uniqueDiffWithinAt hx)
    have hf_diff : DifferentiableOn ℝ f (Set.Icc a b) := by
      intro x hx
      exact (hf_hasDeriv x hx).differentiableWithinAt
    have hcont_deriv : ContinuousOn (derivWithin f (Set.Icc a b)) (Set.Icc a b) := by
      have hEq : Set.EqOn (derivWithin f (Set.Icc a b)) g (Set.Icc a b) := by
        intro x hx
        exact hf_deriv x hx
      exact hcont_g.congr hEq
    have hf_contDiff : ContDiffOn ℝ 1 f (Set.Icc a b) := by
      have hcontDeriv : ContDiffOn ℝ 0 (derivWithin f (Set.Icc a b)) (Set.Icc a b) := by
        simpa [contDiffOn_zero] using hcont_deriv
      refine (contDiffOn_succ_iff_derivWithin
        (s₂ := Set.Icc a b) (f₂ := f) (n := 0) h_unique).2 ?_
      refine ⟨hf_diff, ?_, hcontDeriv⟩
      intro hω
      cases hω
    have hfSeq_eq :
        ∀ n, ∀ x ∈ Set.Icc a b,
          fSeq n x = fSeq n c +
            ∫ t in c..x, derivWithin (fSeq n) (Set.Icc a b) t := by
      intro n x hx
      by_cases hcx : c = x
      · subst hcx
        simp
      have hsubset : Set.uIcc c x ⊆ Set.Icc a b := by
        intro t ht
        have hmin : a ≤ min c x := le_min hc.1 hx.1
        have hmax : max c x ≤ b := max_le hc.2 hx.2
        exact ⟨le_trans hmin ht.1, le_trans ht.2 hmax⟩
      have hcont_uIcc : ContDiffOn ℝ 1 (fSeq n) (Set.uIcc c x) :=
        (hcont n).mono hsubset
      have hFTC :
          ∫ t in c..x, derivWithin (fSeq n) (Set.uIcc c x) t =
            fSeq n x - fSeq n c := by
        simpa using
          (intervalIntegral.integral_derivWithin_uIcc_of_contDiffOn_uIcc
            (f := fSeq n) hcont_uIcc)
      have hunique_uIcc : UniqueDiffOn ℝ (Set.uIcc c x) := by
        by_cases hcx' : c ≤ x
        · have hlt' : c < x := lt_of_le_of_ne hcx' hcx
          simpa [Set.uIcc_of_le hcx'] using (uniqueDiffOn_Icc hlt')
        · have hlt' : x < c := lt_of_not_ge hcx'
          have hle' : x ≤ c := le_of_lt hlt'
          simpa [Set.uIcc_of_ge hle'] using (uniqueDiffOn_Icc hlt')
      have hEq :
          ∀ t ∈ Set.uIcc c x,
            derivWithin (fSeq n) (Set.uIcc c x) t =
              derivWithin (fSeq n) (Set.Icc a b) t := by
        intro t ht
        have hdiff :
            DifferentiableWithinAt ℝ (fSeq n) (Set.Icc a b) t := by
          have hcontWithin := (hcont n) t (hsubset ht)
          exact hcontWithin.differentiableWithinAt (by simp)
        exact derivWithin_subset hsubset (hunique_uIcc.uniqueDiffWithinAt ht) hdiff
      have hEq_ae :
          ∀ᵐ t ∂volume, t ∈ Set.uIoc c x →
            derivWithin (fSeq n) (Set.uIcc c x) t =
              derivWithin (fSeq n) (Set.Icc a b) t := by
        refine Filter.Eventually.of_forall ?_
        intro t ht
        have ht' : t ∈ Set.uIcc c x :=
          (Set.uIoc_subset_uIcc (a := c) (b := x)) ht
        exact hEq t ht'
      have hIntEq :
          ∫ t in c..x, derivWithin (fSeq n) (Set.uIcc c x) t =
            ∫ t in c..x, derivWithin (fSeq n) (Set.Icc a b) t := by
        exact intervalIntegral.integral_congr_ae hEq_ae
      calc
        fSeq n x =
            fSeq n c + ∫ t in c..x, derivWithin (fSeq n) (Set.uIcc c x) t := by
          linarith
        _ = fSeq n c + ∫ t in c..x, derivWithin (fSeq n) (Set.Icc a b) t := by
          simp [hIntEq]
    have hunif : TendstoUniformlyOn fSeq f atTop (Set.Icc a b) := by
      refine (Metric.tendstoUniformlyOn_iff).2 ?_
      intro ε hε
      have hba : 0 < b - a := sub_pos.mpr hlt
      have hε2 : 0 < ε / 2 := by linarith
      have hC : 0 < ε / (2 * (b - a)) := by
        have hden : 0 < 2 * (b - a) := by nlinarith [hba]
        exact div_pos hε hden
      have hval' : ∀ᶠ n in atTop, |fSeq n c - l| < ε / 2 := by
        have h :=
          (tendsto_atTop_nhds.1 hl) (Metric.ball l (ε / 2))
            (by simpa [Metric.mem_ball] using hε2) Metric.isOpen_ball
        rcases h with ⟨N, hN⟩
        refine (eventually_atTop.2 ⟨N, ?_⟩)
        intro n hn
        have hmem := hN n hn
        have hdist : dist (fSeq n c) l < ε / 2 := by
          simpa [Metric.mem_ball] using hmem
        simpa [Real.dist_eq, abs_sub_comm] using hdist
      have hderiv' :
          ∀ᶠ n in atTop, ∀ x ∈ Set.Icc a b,
            |g x - derivWithin (fSeq n) (Set.Icc a b) x| < ε / (2 * (b - a)) := by
        have h := (Metric.tendstoUniformlyOn_iff.mp hderiv) (ε / (2 * (b - a))) hC
        refine h.mono ?_
        intro n hn x hx
        have hdist := hn x hx
        simpa [Real.dist_eq, abs_sub_comm] using hdist
      refine (hval'.and hderiv').mono ?_
      intro n hn x hx
      have hsubset : Set.uIcc c x ⊆ Set.Icc a b := by
        intro t ht
        have hmin : a ≤ min c x := le_min hc.1 hx.1
        have hmax : max c x ≤ b := max_le hc.2 hx.2
        exact ⟨le_trans hmin ht.1, le_trans ht.2 hmax⟩
      have hcont_uIcc : ContinuousOn g (Set.uIcc c x) := hcont_g.mono hsubset
      have hInt_g : IntervalIntegrable g volume c x :=
        hcont_uIcc.intervalIntegrable (μ := volume)
      have hcont_deriv_n :
          ContinuousOn (fun t => derivWithin (fSeq n) (Set.Icc a b) t) (Set.Icc a b) :=
        (hcont n).continuousOn_derivWithin h_unique (by simp)
      have hInt_deriv :
          IntervalIntegrable (fun t => derivWithin (fSeq n) (Set.Icc a b) t) volume c x := by
        have hcont_uIcc' : ContinuousOn
            (fun t => derivWithin (fSeq n) (Set.Icc a b) t) (Set.uIcc c x) :=
          hcont_deriv_n.mono hsubset
        exact hcont_uIcc'.intervalIntegrable (μ := volume)
      have hInt_sub :
          (∫ t in c..x, g t) - (∫ t in c..x, derivWithin (fSeq n) (Set.Icc a b) t) =
            ∫ t in c..x, (g t - derivWithin (fSeq n) (Set.Icc a b) t) := by
        simpa [sub_eq_add_neg] using
          (intervalIntegral.integral_sub (f := g)
            (g := fun t => derivWithin (fSeq n) (Set.Icc a b) t) hInt_g hInt_deriv).symm
      have hbound_int :
          |∫ t in c..x, (g t - derivWithin (fSeq n) (Set.Icc a b) t)| ≤
            (ε / (2 * (b - a))) * |x - c| := by
        have hbound' :
            ‖∫ t in c..x, (g t - derivWithin (fSeq n) (Set.Icc a b) t)‖ ≤
              (ε / (2 * (b - a))) * |x - c| := by
          refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
          intro t ht
          have ht' : t ∈ Set.Icc a b := hsubset
            ((Set.uIoc_subset_uIcc (a := c) (b := x)) ht)
          have hgt := hn.2 t ht'
          have hgt' : ‖g t - derivWithin (fSeq n) (Set.Icc a b) t‖ ≤
              ε / (2 * (b - a)) := by
            exact le_of_lt (by simpa [Real.norm_eq_abs] using hgt)
          exact hgt'
        simpa [Real.norm_eq_abs] using hbound'
      have hxc : |x - c| ≤ b - a := by
        exact abs_sub_le_of_le_of_le hx.1 hx.2 hc.1 hc.2
      have hposC : 0 ≤ ε / (2 * (b - a)) := le_of_lt hC
      have hbound_int' :
          |∫ t in c..x, (g t - derivWithin (fSeq n) (Set.Icc a b) t)| ≤ ε / 2 := by
        have hmul := mul_le_mul_of_nonneg_left hxc hposC
        have hmul' :
            (ε / (2 * (b - a))) * |x - c| ≤ (ε / (2 * (b - a))) * (b - a) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
        have hmul'' :
            (ε / (2 * (b - a))) * (b - a) = ε / 2 := by
          have hne : b - a ≠ 0 := by linarith [hlt]
          field_simp [hne, mul_comm, mul_left_comm, mul_assoc]
        exact le_trans hbound_int (by simpa [hmul''] using hmul')
      have hdiff :
          |f x - fSeq n x| ≤
            |l - fSeq n c| +
              |∫ t in c..x, (g t - derivWithin (fSeq n) (Set.Icc a b) t)| := by
        have hseq := hfSeq_eq n x hx
        calc
          |f x - fSeq n x| =
              |(l + ∫ t in c..x, g t) -
                (fSeq n c + ∫ t in c..x, derivWithin (fSeq n) (Set.Icc a b) t)| := by
            simp [f, hseq]
          _ =
              |(l - fSeq n c) +
                ((∫ t in c..x, g t) -
                  (∫ t in c..x, derivWithin (fSeq n) (Set.Icc a b) t))| := by
            ring_nf
          _ ≤
              |l - fSeq n c| +
                |(∫ t in c..x, g t) -
                  (∫ t in c..x, derivWithin (fSeq n) (Set.Icc a b) t)| := by
            exact abs_add_le _ _
          _ =
              |l - fSeq n c| +
                |∫ t in c..x, (g t - derivWithin (fSeq n) (Set.Icc a b) t)| := by
            simp [hInt_sub]
      have hsum :
          |l - fSeq n c| +
            |∫ t in c..x, (g t - derivWithin (fSeq n) (Set.Icc a b) t)| < ε := by
        have hsum' :
            |l - fSeq n c| +
              |∫ t in c..x, (g t - derivWithin (fSeq n) (Set.Icc a b) t)| <
                ε / 2 + ε / 2 :=
          add_lt_add_of_lt_of_le (by simpa [abs_sub_comm] using hn.1) hbound_int'
        have hsum'' : ε / 2 + ε / 2 = ε := by ring
        simpa [hsum''] using hsum'
      have hdist : dist (f x) (fSeq n x) < ε := by
        have h := lt_of_le_of_lt hdiff hsum
        simpa [Real.dist_eq] using h
      exact hdist
    refine ⟨f, hf_contDiff, hunif, hf_deriv⟩
  · have hEq : a = b := le_antisymm hab (le_of_not_gt hlt)
    have hc_eq : c = a := by
      have hc' : c ∈ Set.Icc a a := by simpa [hEq] using hc
      simpa [Set.Icc_self] using hc'
    have hnot_acc : ¬ AccPt a (𝓟 (Set.Icc a b)) := by
      intro hacc
      have : (⊥ : Filter ℝ).NeBot := by
        simpa [hEq, Set.Icc_self] using (accPt_principal_iff_nhdsWithin.mp hacc)
      exact (not_neBot.mpr rfl) this
    have hderiv_zero :
        ∀ n, derivWithin (fSeq n) (Set.Icc a b) a = 0 := by
      intro n
      exact derivWithin_zero_of_not_accPt hnot_acc
    have hg_zero : g a = 0 := by
      have hpoint :
          Tendsto (fun n => derivWithin (fSeq n) (Set.Icc a b) a) atTop (𝓝 (g a)) := by
        have hab' : a ≤ b := by simp [hEq]
        exact hderiv.tendsto_at (Set.left_mem_Icc.2 hab')
      have hpoint0 :
          Tendsto (fun n => derivWithin (fSeq n) (Set.Icc a b) a) atTop (𝓝 (0 : ℝ)) := by
        refine (tendsto_congr ?_).2 tendsto_const_nhds
        intro n
        simpa using hderiv_zero n
      exact tendsto_nhds_unique hpoint hpoint0
    let f : ℝ → ℝ := fun _ => l
    have hf_contDiff : ContDiffOn ℝ 1 f (Set.Icc a b) := by
      simpa using (contDiffOn_const (s := Set.Icc a b) (c := l))
    have hunif : TendstoUniformlyOn fSeq f atTop (Set.Icc a b) := by
      refine (Metric.tendstoUniformlyOn_iff).2 ?_
      intro ε hε
      have hl' : Tendsto (fun n => fSeq n a) atTop (𝓝 l) := by
        simpa [hc_eq] using hl
      have h :=
        (tendsto_atTop_nhds.1 hl') (Metric.ball l ε) (by simpa [Metric.mem_ball] using hε)
          Metric.isOpen_ball
      rcases h with ⟨N, hN⟩
      refine (eventually_atTop.2 ⟨N, ?_⟩)
      intro n hn x hx
      have hx' : x = a := by
        have hx'' : x ∈ Set.Icc a a := by simpa [hEq] using hx
        simpa [Set.Icc_self] using hx''
      have hmem := hN n hn
      have hdist : dist (fSeq n a) l < ε := by
        simpa [Metric.mem_ball] using hmem
      simpa [f, hx', dist_comm] using hdist
    have hf_deriv : ∀ x ∈ Set.Icc a b, derivWithin f (Set.Icc a b) x = g x := by
      intro x hx
      have hx' : x = a := by
        have hx'' : x ∈ Set.Icc a a := by simpa [hEq] using hx
        simpa [Set.Icc_self] using hx''
      have hderivf : derivWithin f (Set.Icc a b) a = 0 := by
        exact derivWithin_zero_of_not_accPt hnot_acc
      simp [hx', hg_zero, hderivf]
    exact ⟨f, hf_contDiff, hunif, hf_deriv⟩

/-- Proposition 6.2.11: A power series `∑ cₙ (x - a)^n` with radius of
convergence `ρ > 0` converges uniformly on `[a - r, a + r]` for every
`0 < r < ρ`. As a consequence, the sum defines a continuous function on the
open interval where the series converges (or on all of `ℝ` if `ρ = ∞`). -/
theorem powerSeries_uniform_on_compact {a : ℝ} {c : ℕ → ℝ} {ρ r : ℝ}
    (hr : 0 < r) (hrρ : r < ρ)
    (hconv : ∀ x ∈ Set.Icc (a - ρ) (a + ρ),
      Summable fun n => c n * (x - a) ^ n) :
    TendstoUniformlyOn
      (fun N x => Finset.sum (Finset.range N) (fun n => c n * (x - a) ^ n))
      (fun x => tsum fun n => c n * (x - a) ^ n) atTop (Set.Icc (a - r) (a + r)) := by
  have hr_nonneg : 0 ≤ r := le_of_lt hr
  have hmem : a + r ∈ Set.Icc (a - ρ) (a + ρ) := by
    constructor
    · linarith
    · linarith [hrρ]
  have hsum_ar : Summable (fun n => c n * r ^ n) := by
    simpa [add_sub_cancel_left] using (hconv (a + r) hmem)
  have hsum_u : Summable (fun n => |c n| * r ^ n) := by
    simpa [abs_mul, abs_pow, abs_of_nonneg hr_nonneg] using hsum_ar.abs
  have h_abs_sub : ∀ {x}, x ∈ Set.Icc (a - r) (a + r) → |x - a| ≤ r := by
    intro x hx
    have hx' : a - r ≤ x ∧ x ≤ a + r := by
      simpa [Set.mem_Icc] using hx
    have hx1 : -r ≤ x - a := by linarith [hx'.1]
    have hx2 : x - a ≤ r := by linarith [hx'.2]
    exact (abs_le.mpr ⟨hx1, hx2⟩)
  have hterm :
      ∀ n x, x ∈ Set.Icc (a - r) (a + r) →
        ‖c n * (x - a) ^ n‖ ≤ |c n| * r ^ n := by
    intro n x hx
    have hxabs : |x - a| ≤ r := h_abs_sub hx
    have hxabs' : ‖x - a‖ ≤ r := by
      simpa [Real.norm_eq_abs] using hxabs
    have hpow : ‖x - a‖ ^ n ≤ r ^ n :=
      pow_le_pow_left₀ (by exact norm_nonneg _) hxabs' n
    have hcnonneg : 0 ≤ ‖c n‖ := norm_nonneg _
    calc
      ‖c n * (x - a) ^ n‖ = ‖c n‖ * ‖(x - a) ^ n‖ := by
        simp
      _ = ‖c n‖ * ‖x - a‖ ^ n := by simp [norm_pow]
      _ ≤ ‖c n‖ * r ^ n := by exact mul_le_mul_of_nonneg_left hpow hcnonneg
      _ = |c n| * r ^ n := by simp [Real.norm_eq_abs]
  refine tendstoUniformlyOn_tsum_nat
      (f := fun n x => c n * (x - a) ^ n)
      (u := fun n => |c n| * r ^ n)
      (s := Set.Icc (a - r) (a + r))
      hsum_u ?_
  intro n x hx
  exact hterm n x hx

/-- A convergent power series `∑ cₙ (x - a)^n` defines a continuous function on
the open interval of convergence, or on all of `ℝ` when the radius is infinite. -/
theorem powerSeries_sum_continuous {a : ℝ} {c : ℕ → ℝ} {ρ : ℝ}
    (hconv : ∀ x ∈ Set.Ioo (a - ρ) (a + ρ),
      Summable fun n => c n * (x - a) ^ n) :
    ContinuousOn (fun x => tsum fun n => c n * (x - a) ^ n) (Set.Ioo (a - ρ) (a + ρ)) := by
  have hopen : IsOpen (Set.Ioo (a - ρ) (a + ρ)) := isOpen_Ioo
  refine (IsOpen.continuousOn_iff hopen).2 ?_
  intro x hx
  have hxabs : |x - a| < ρ := by
    have hx1 : a - ρ < x := hx.1
    have hx2 : x < a + ρ := hx.2
    have hx1' : -ρ < x - a := by linarith
    have hx2' : x - a < ρ := by linarith
    exact abs_lt.mpr ⟨hx1', hx2'⟩
  obtain ⟨r, hrx, hrρ⟩ := exists_between hxabs
  have hrpos : 0 < r := lt_of_le_of_lt (abs_nonneg _) hrx
  have hmem : a + r ∈ Set.Ioo (a - ρ) (a + ρ) := by
    constructor
    · linarith [hrpos]
    · linarith [hrρ]
  have hsum_ar : Summable (fun n => c n * r ^ n) := by
    simpa [add_sub_cancel_left] using (hconv (a + r) hmem)
  have hsum_u : Summable (fun n => |c n| * r ^ n) := by
    simpa [abs_mul, abs_pow, abs_of_nonneg (le_of_lt hrpos)] using hsum_ar.abs
  have h_abs_sub : ∀ {x}, x ∈ Set.Icc (a - r) (a + r) → |x - a| ≤ r := by
    intro x hx
    have hx' : a - r ≤ x ∧ x ≤ a + r := by
      simpa [Set.mem_Icc] using hx
    have hx1 : -r ≤ x - a := by linarith [hx'.1]
    have hx2 : x - a ≤ r := by linarith [hx'.2]
    exact abs_le.mpr ⟨hx1, hx2⟩
  have hterm :
      ∀ n x, x ∈ Set.Icc (a - r) (a + r) →
        ‖c n * (x - a) ^ n‖ ≤ |c n| * r ^ n := by
    intro n x hx
    have hxabs : |x - a| ≤ r := h_abs_sub hx
    have hxabs' : ‖x - a‖ ≤ r := by
      simpa [Real.norm_eq_abs] using hxabs
    have hpow : ‖x - a‖ ^ n ≤ r ^ n :=
      pow_le_pow_left₀ (by exact norm_nonneg _) hxabs' n
    have hcnonneg : 0 ≤ ‖c n‖ := norm_nonneg _
    calc
      ‖c n * (x - a) ^ n‖ = ‖c n‖ * ‖(x - a) ^ n‖ := by
        simp
      _ = ‖c n‖ * ‖x - a‖ ^ n := by simp [norm_pow]
      _ ≤ ‖c n‖ * r ^ n := by exact mul_le_mul_of_nonneg_left hpow hcnonneg
      _ = |c n| * r ^ n := by simp [Real.norm_eq_abs]
  have hcont :
      ∀ n, ContinuousOn (fun x => c n * (x - a) ^ n) (Set.Icc (a - r) (a + r)) := by
    intro n
    have hcont' : Continuous fun x => c n * (x - a) ^ n := by
      fun_prop
    exact hcont'.continuousOn
  have hcontOn :
      ContinuousOn (fun x => tsum fun n => c n * (x - a) ^ n)
        (Set.Icc (a - r) (a + r)) := by
    refine continuousOn_tsum hcont hsum_u ?_
    intro n x hx
    exact hterm n x hx
  have hxlt : a - r < x := by
    have hx' : -r < x - a := (abs_lt.mp hrx).1
    linarith
  have hxgt : x < a + r := by
    have hx' : x - a < r := (abs_lt.mp hrx).2
    linarith
  have hnhds : Set.Icc (a - r) (a + r) ∈ 𝓝 x := Icc_mem_nhds hxlt hxgt
  exact hcontOn.continuousAt hnhds

@[simp] lemma abs_nat_succ_real (n : ℕ) : |(Nat.succ n : ℝ)| = (Nat.succ n : ℝ) := by
  have h : 0 ≤ (Nat.succ n : ℝ) := by exact_mod_cast (Nat.zero_le (Nat.succ n))
  simpa using (abs_of_nonneg h)

/-- Corollary 6.2.12: For a convergent power series
`∑_{n=0}^∞ cₙ (x - a)^n` with radius of convergence `ρ > 0`, if `I` is the
interval `(a - ρ, a + ρ)` (or `ℝ` when `ρ = ∞`) and `f` denotes the limit,
then for every `x ∈ I` one has
`∫ₐˣ f = ∑_{n=1}^∞ (c_{n-1} / n) (x - a)^n`, and the radius of convergence of
the latter series is at least `ρ`. -/
theorem integral_powerSeries_eq_series {a ρ : ℝ} {c : ℕ → ℝ}
    (hρ : 0 < ρ)
    (hconv : ∀ x ∈ Set.Ioo (a - ρ) (a + ρ),
      Summable fun n => c n * (x - a) ^ n) :
    ∀ x ∈ Set.Ioo (a - ρ) (a + ρ),
      (∫ t in a..x, tsum fun n => c n * (t - a) ^ n) =
        tsum fun n => (c n) / (Nat.succ n : ℝ) * (x - a) ^ (Nat.succ n) := by
  classical
  intro x hx
  have _hρ : 0 < ρ := hρ
  have hxabs : |x - a| < ρ := by
    have hx1 : a - ρ < x := hx.1
    have hx2 : x < a + ρ := hx.2
    have hx1' : -ρ < x - a := by linarith
    have hx2' : x - a < ρ := by linarith
    exact abs_lt.mpr ⟨hx1', hx2'⟩
  obtain ⟨r, hrx, hrρ⟩ := exists_between hxabs
  have hrpos : 0 < r := lt_of_le_of_lt (abs_nonneg _) hrx
  obtain ⟨ρ', hrρ', hρ'ρ⟩ := exists_between hrρ
  have hconv' : ∀ y ∈ Set.Icc (a - ρ') (a + ρ'),
      Summable fun n => c n * (y - a) ^ n := by
    intro y hy
    have hy' : y ∈ Set.Ioo (a - ρ) (a + ρ) := by
      constructor <;> linarith [hy.1, hy.2, hρ'ρ]
    exact hconv y hy'
  let partialSum : ℕ → ℝ → ℝ :=
    fun N x => Finset.sum (Finset.range N) (fun n => c n * (x - a) ^ n)
  have hunif :
      TendstoUniformlyOn
        partialSum
        (fun x => tsum fun n => c n * (x - a) ^ n) atTop (Set.Icc (a - r) (a + r)) := by
    simpa [partialSum] using
      (powerSeries_uniform_on_compact (a := a) (c := c) (ρ := ρ') (r := r)
        hrpos hrρ' hconv')
  have hcont_sum :
      ∀ N, Continuous fun t : ℝ => partialSum N t := by
    intro N
    classical
    change Continuous fun t : ℝ =>
      Finset.sum (Finset.range N) (fun n => c n * (t - a) ^ n)
    refine continuous_finset_sum _ ?_
    intro n hn
    fun_prop
  have hint_ax :
      ∀ N, IntervalIntegrable (fun t : ℝ => partialSum N t)
        volume a x := by
    intro N
    exact (hcont_sum N).intervalIntegrable (a := a) (b := x)
  have hint_xa :
      ∀ N, IntervalIntegrable (fun t : ℝ => partialSum N t)
        volume x a := by
    intro N
    exact (hcont_sum N).intervalIntegrable (a := x) (b := a)
  have integral_pow_sub :
      ∀ n : ℕ, ∫ t in a..x, (t - a) ^ n =
        (x - a) ^ (Nat.succ n) / (Nat.succ n : ℝ) := by
    intro n
    calc
      ∫ t in a..x, (t - a) ^ n = ∫ u in (a - a)..(x - a), u ^ n := by
        simpa using
          (intervalIntegral.integral_comp_sub_right (f := fun u : ℝ => u ^ n)
            (a := a) (b := x) (d := a))
      _ = ((x - a) ^ (Nat.succ n) - (a - a) ^ (Nat.succ n)) / (Nat.succ n : ℝ) := by
        simp [integral_pow, Nat.succ_eq_add_one]
      _ = (x - a) ^ (Nat.succ n) / (Nat.succ n : ℝ) := by
        simp
  have integral_term :
      ∀ n : ℕ, ∫ t in a..x, c n * (t - a) ^ n =
        (c n) / (Nat.succ n : ℝ) * (x - a) ^ (Nat.succ n) := by
    intro n
    calc
      ∫ t in a..x, c n * (t - a) ^ n =
          c n * ∫ t in a..x, (t - a) ^ n := by
        exact
          (intervalIntegral.integral_const_mul (a := a) (b := x) (r := c n)
            (f := fun t : ℝ => (t - a) ^ n))
      _ = c n * ((x - a) ^ (Nat.succ n) / (Nat.succ n : ℝ)) := by
        simp [integral_pow_sub]
      _ = (c n) / (Nat.succ n : ℝ) * (x - a) ^ (Nat.succ n) := by
        simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  have hsum_integral :
      ∀ N, ∫ t in a..x, partialSum N t =
        Finset.sum (Finset.range N) (fun n =>
          (c n) / (Nat.succ n : ℝ) * (x - a) ^ (Nat.succ n)) := by
    intro N
    have h_int :
        ∀ n ∈ Finset.range N,
          IntervalIntegrable (fun t : ℝ => c n * (t - a) ^ n) volume a x := by
      intro n hn
      have hcont : Continuous fun t : ℝ => c n * (t - a) ^ n := by
        fun_prop
      exact (hcont.intervalIntegrable (a := a) (b := x))
    calc
      ∫ t in a..x, partialSum N t =
          Finset.sum (Finset.range N) (fun n => ∫ t in a..x, c n * (t - a) ^ n) := by
        simpa [partialSum] using
          (intervalIntegral.integral_finset_sum (a := a) (b := x) (μ := volume)
            (s := Finset.range N) (f := fun n (t : ℝ) => c n * (t - a) ^ n) h_int)
      _ = Finset.sum (Finset.range N)
          (fun n => (c n) / (Nat.succ n : ℝ) * (x - a) ^ (Nat.succ n)) := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        exact integral_term n
  have hlim_integral :
      Tendsto
        (fun N =>
          ∫ t in a..x, partialSum N t) atTop
        (𝓝 (∫ t in a..x, tsum fun n => c n * (t - a) ^ n)) := by
    by_cases hxle : a ≤ x
    · have hxlt : x < a + r := by
        have hx' : x - a < r := (abs_lt.mp hrx).2
        linarith
      have hsub : Set.Icc a x ⊆ Set.Icc (a - r) (a + r) := by
        intro t ht
        have hlow : a - r ≤ t := by linarith [ht.1]
        have hhigh : t ≤ a + r := by linarith [ht.2, hxlt]
        exact ⟨hlow, hhigh⟩
      have hunif_ax :
          TendstoUniformlyOn
            partialSum
            (fun x => tsum fun n => c n * (x - a) ^ n) atTop (Set.Icc a x) :=
        hunif.mono hsub
      exact
        (integral_interval_tendsto_of_uniform_limit (a := a) (b := x)
          (fSeq := partialSum)
          (f := fun x => tsum fun n => c n * (x - a) ^ n)
          hint_ax hunif_ax hxle).2
    · have hxle' : x ≤ a := le_of_not_ge hxle
      have hxgt : a - r < x := by
        have hx' : -r < x - a := (abs_lt.mp hrx).1
        linarith
      have hsub : Set.Icc x a ⊆ Set.Icc (a - r) (a + r) := by
        intro t ht
        have hlow : a - r ≤ t := by linarith [ht.1, hxgt]
        have hhigh : t ≤ a + r := by
          have hle : a ≤ a + r := by linarith [le_of_lt hrpos]
          linarith [ht.2, hle]
        exact ⟨hlow, hhigh⟩
      have hunif_xa :
          TendstoUniformlyOn
            partialSum
            (fun x => tsum fun n => c n * (x - a) ^ n) atTop (Set.Icc x a) :=
        hunif.mono hsub
      have hlim_xa :
          Tendsto
            (fun N =>
              ∫ t in x..a, partialSum N t) atTop
            (𝓝 (∫ t in x..a, tsum fun n => c n * (t - a) ^ n)) :=
        (integral_interval_tendsto_of_uniform_limit (a := x) (b := a)
          (fSeq := partialSum)
          (f := fun x => tsum fun n => c n * (x - a) ^ n)
          hint_xa hunif_xa hxle').2
      have hfun :
          (fun N => ∫ t in a..x, partialSum N t) =
            fun N => -∫ t in x..a, partialSum N t := by
        funext N
        rw [intervalIntegral.integral_symm]
      have hlim_fun :
          Tendsto (fun N => ∫ t in a..x, partialSum N t) atTop
            (𝓝 (-∫ t in x..a, tsum fun n => c n * (t - a) ^ n)) := by
        simpa [hfun] using hlim_xa.neg
      have hlim_lim :
          (∫ t in a..x, tsum fun n => c n * (t - a) ^ n) =
            -∫ t in x..a, tsum fun n => c n * (t - a) ^ n :=
        intervalIntegral.integral_symm
          (f := fun t => tsum fun n => c n * (t - a) ^ n) x a
      have hlim_ax :
          Tendsto (fun N => ∫ t in a..x, partialSum N t) atTop
            (𝓝 (∫ t in a..x, tsum fun n => c n * (t - a) ^ n)) := by
        exact hlim_lim ▸ hlim_fun
      exact hlim_ax
  have hlim_sum :
      Tendsto (fun N =>
        Finset.sum (Finset.range N)
          (fun n => (c n) / (Nat.succ n : ℝ) * (x - a) ^ (Nat.succ n))) atTop
        (𝓝 (∫ t in a..x, tsum fun n => c n * (t - a) ^ n)) := by
    refine (tendsto_congr ?_).2 hlim_integral
    intro N
    symm
    exact hsum_integral N
  have hmem : a + r ∈ Set.Ioo (a - ρ) (a + ρ) := by
    constructor
    · linarith [hrpos]
    · linarith [hrρ]
  have hsum_ar : Summable (fun n => c n * r ^ n) := by
    simpa [add_sub_cancel_left] using (hconv (a + r) hmem)
  have hsum_abs : Summable (fun n => |c n| * r ^ n) := by
    simpa [abs_mul, abs_pow, abs_of_nonneg (le_of_lt hrpos)] using hsum_ar.abs
  have hsum_bound : Summable (fun n => |c n| * r ^ (Nat.succ n)) := by
    have h := hsum_abs.mul_left r
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h
  have hsum :
      Summable fun n =>
        (c n) / (Nat.succ n : ℝ) * (x - a) ^ (Nat.succ n) := by
    refine Summable.of_norm_bounded hsum_bound ?_
    intro n
    have hpos : 0 < (Nat.succ n : ℝ) := by
      exact_mod_cast (Nat.succ_pos n)
    have hdiv : |c n| / (Nat.succ n : ℝ) ≤ |c n| := by
      have h1 : (1 : ℝ) ≤ (Nat.succ n : ℝ) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
      exact div_le_self (abs_nonneg _) h1
    have habs : |(Nat.succ n : ℝ)| = (Nat.succ n : ℝ) := by
      exact abs_of_nonneg (by exact_mod_cast (Nat.zero_le (Nat.succ n)))
    have hxabs' : |x - a| ≤ r := le_of_lt hrx
    have hpow : |x - a| ^ (Nat.succ n) ≤ r ^ (Nat.succ n) :=
      pow_le_pow_left₀ (abs_nonneg _) hxabs' (Nat.succ n)
    have hnorm :
        ‖(c n) / (Nat.succ n : ℝ) * (x - a) ^ (Nat.succ n)‖ =
          |c n| / (Nat.succ n : ℝ) * |x - a| ^ (Nat.succ n) := by
      have hnorm_div :
          ‖(c n) / (Nat.succ n : ℝ)‖ = |c n| / (Nat.succ n : ℝ) := by
        calc
          ‖(c n) / (Nat.succ n : ℝ)‖ = |c n| / |(Nat.succ n : ℝ)| := by
            simp [Real.norm_eq_abs, div_eq_mul_inv]
          _ = |c n| / (Nat.succ n : ℝ) := by
            have hnonneg : 0 ≤ (n : ℝ) + 1 := by
              have h : 0 ≤ (n : ℝ) := by
                exact_mod_cast (Nat.zero_le n)
              linarith
            have hpos : |(n : ℝ) + 1| = (n : ℝ) + 1 := abs_of_nonneg hnonneg
            simp [Nat.succ_eq_add_one, hpos]
      have hnorm_pow :
          ‖(x - a) ^ (Nat.succ n)‖ = |x - a| ^ (Nat.succ n) := by
        simp [norm_pow, Real.norm_eq_abs]
      calc
        ‖(c n) / (Nat.succ n : ℝ) * (x - a) ^ (Nat.succ n)‖
            = ‖(c n) / (Nat.succ n : ℝ)‖ * ‖(x - a) ^ (Nat.succ n)‖ := by
              simp [norm_mul]
        _ = (|c n| / (Nat.succ n : ℝ)) * |x - a| ^ (Nat.succ n) := by
              rw [hnorm_div, hnorm_pow]
    calc
      ‖(c n) / (Nat.succ n : ℝ) * (x - a) ^ (Nat.succ n)‖ =
          |c n| / (Nat.succ n : ℝ) * |x - a| ^ (Nat.succ n) := hnorm
      _ ≤ |c n| * r ^ (Nat.succ n) := by
        have hnonneg : 0 ≤ |x - a| ^ (Nat.succ n) := by
          exact pow_nonneg (abs_nonneg _) (Nat.succ n)
        exact mul_le_mul hdiv hpow hnonneg (abs_nonneg _)
  have hlim_sum' :
      Tendsto (fun N =>
        Finset.sum (Finset.range N)
          (fun n => (c n) / (Nat.succ n : ℝ) * (x - a) ^ (Nat.succ n))) atTop
        (𝓝 (tsum fun n => (c n) / (Nat.succ n : ℝ) * (x - a) ^ (Nat.succ n))) :=
    hsum.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hlim_sum hlim_sum'

/-- Corollary 6.2.13: For a convergent power series
`∑_{n=0}^∞ cₙ (x - a)^n` with radius of convergence `ρ > 0`, let
`I = (a - ρ, a + ρ)`.  If `f` is its sum on `I`, then `f` is differentiable on
`I` and `f' (x) = ∑_{n=0}^∞ (n + 1) c_{n+1} (x - a)^n`, whose radius of
convergence is also `ρ`. -/
theorem deriv_powerSeries_eq_series {a ρ : ℝ} {c : ℕ → ℝ}
    (hconv : ∀ x ∈ Set.Ioo (a - ρ) (a + ρ),
      Summable fun n => c n * (x - a) ^ n) :
    ∀ x ∈ Set.Ioo (a - ρ) (a + ρ),
      DifferentiableAt ℝ (fun y : ℝ => tsum fun n => c n * (y - a) ^ n) x ∧
        deriv (fun y : ℝ => tsum fun n => c n * (y - a) ^ n) x =
          (tsum fun n => (Nat.succ n : ℝ) * c (Nat.succ n) * (x - a) ^ n) ∧
        Summable fun n => (Nat.succ n : ℝ) * c (Nat.succ n) * (x - a) ^ n := by
  classical
  intro x hx
  have hxabs : |x - a| < ρ := by
    have hx1 : a - ρ < x := hx.1
    have hx2 : x < a + ρ := hx.2
    have hx1' : -ρ < x - a := by linarith
    have hx2' : x - a < ρ := by linarith
    exact abs_lt.mpr ⟨hx1', hx2'⟩
  obtain ⟨r, hrx, hrρ⟩ := exists_between hxabs
  have hrpos : 0 < r := lt_of_le_of_lt (abs_nonneg _) hrx
  obtain ⟨ρ', hrρ', hρ'ρ⟩ := exists_between hrρ
  have hρ'pos : 0 < ρ' := lt_trans hrpos hrρ'
  have hconv' : ∀ y ∈ Set.Icc (a - ρ') (a + ρ'),
      Summable fun n => c n * (y - a) ^ n := by
    intro y hy
    have hy' : y ∈ Set.Ioo (a - ρ) (a + ρ) := by
      constructor <;> linarith [hy.1, hy.2, hρ'ρ]
    exact hconv y hy'
  let partialSum : ℕ → ℝ → ℝ :=
    fun N x => Finset.sum (Finset.range N) (fun n => c n * (x - a) ^ n)
  let derivTerm : ℕ → ℝ → ℝ :=
    fun n x => (Nat.succ n : ℝ) * c (Nat.succ n) * (x - a) ^ n
  let partialDeriv : ℕ → ℝ → ℝ :=
    fun N x => Finset.sum (Finset.range N) (fun n => derivTerm n x)
  let fSeq : ℕ → ℝ → ℝ := fun N x => partialSum (Nat.succ N) x
  let g : ℝ → ℝ := fun x => tsum fun n => derivTerm n x
  have hunif :
      TendstoUniformlyOn partialSum
        (fun x => tsum fun n => c n * (x - a) ^ n) atTop (Set.Icc (a - r) (a + r)) := by
    simpa [partialSum] using
      (powerSeries_uniform_on_compact (a := a) (c := c) (ρ := ρ') (r := r)
        hrpos hrρ' hconv')
  have h_abs_sub : ∀ {x}, x ∈ Set.Icc (a - r) (a + r) → |x - a| ≤ r := by
    intro x hx
    have hx' : a - r ≤ x ∧ x ≤ a + r := by
      simpa [Set.mem_Icc] using hx
    have hx1 : -r ≤ x - a := by linarith [hx'.1]
    have hx2 : x - a ≤ r := by linarith [hx'.2]
    exact (abs_le.mpr ⟨hx1, hx2⟩)
  have hmem' : a + ρ' ∈ Set.Icc (a - ρ') (a + ρ') := by
    constructor <;> linarith [hρ'pos]
  have hsum_ar : Summable (fun n => c n * ρ' ^ n) := by
    simpa [add_sub_cancel_left] using (hconv' (a + ρ') hmem')
  have hsum_abs : Summable (fun n => |c n| * ρ' ^ n) := by
    simpa [abs_mul, abs_pow, abs_of_nonneg (le_of_lt hρ'pos)] using hsum_ar.abs
  have hsum_u : Summable (fun n => |c (Nat.succ n)| * ρ' ^ (Nat.succ n)) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (summable_nat_add_iff (f := fun n => |c n| * ρ' ^ n) 1).2 hsum_abs
  have hq_nonneg : 0 ≤ r / ρ' := by
    exact div_nonneg (le_of_lt hrpos) (le_of_lt hρ'pos)
  have hq_lt : r / ρ' < 1 := by
    exact (div_lt_one hρ'pos).2 hrρ'
  have hlim :
      Tendsto (fun n : ℕ => (Nat.succ n : ℝ) * (r / ρ') ^ n) atTop (𝓝 0) := by
    have hlim1 :
        Tendsto (fun n : ℕ => (n : ℝ) * (r / ρ') ^ n) atTop (𝓝 0) :=
      tendsto_self_mul_const_pow_of_lt_one hq_nonneg hq_lt
    have hlim2 :
        Tendsto (fun n : ℕ => (r / ρ') ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt
    have hlim_add :
        Tendsto (fun n : ℕ => (n : ℝ) * (r / ρ') ^ n + (r / ρ') ^ n) atTop (𝓝 0) := by
      simpa using hlim1.add hlim2
    refine (tendsto_congr ?_).1 hlim_add
    intro n
    simp [Nat.succ_eq_add_one, add_mul, one_mul, add_comm]
  rcases (Metric.tendsto_atTop.1 hlim) ρ' hρ'pos with ⟨N, hN⟩
  have hterm_bound :
      ∀ᶠ n in atTop, ∀ x ∈ Set.Icc (a - r) (a + r),
        ‖derivTerm n x‖ ≤ |c (Nat.succ n)| * ρ' ^ (Nat.succ n) := by
    refine (eventually_atTop.2 ⟨N, ?_⟩)
    intro n hn x hx
    have hle_q : (Nat.succ n : ℝ) * (r / ρ') ^ n ≤ ρ' := by
      have habs : |(Nat.succ n : ℝ)| * (|r| / |ρ'|) ^ n < ρ' := by
        simpa [dist_eq_norm, Real.norm_eq_abs] using hN n hn
      have hr_nonneg : 0 ≤ r := le_of_lt hrpos
      have hρ'_nonneg : 0 ≤ ρ' := le_of_lt hρ'pos
      have hle_q' :
          (Nat.succ n : ℝ) * (r / ρ') ^ n < ρ' := by
        have hnat_nonneg : 0 ≤ (n : ℝ) + 1 := by
          have h : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
          linarith
        simpa [abs_of_nonneg hnat_nonneg, abs_of_nonneg hr_nonneg,
          abs_of_nonneg hρ'_nonneg] using habs
      exact le_of_lt hle_q'
    have hxabs : |x - a| ≤ r := h_abs_sub hx
    have hpow : |x - a| ^ n ≤ r ^ n :=
      pow_le_pow_left₀ (abs_nonneg _) hxabs n
    have hle_r : (Nat.succ n : ℝ) * r ^ n ≤ ρ' ^ (Nat.succ n) := by
      have hρ'pow_nonneg : 0 ≤ ρ' ^ n := by
        exact pow_nonneg (le_of_lt hρ'pos) n
      have hle_q' := mul_le_mul_of_nonneg_right hle_q hρ'pow_nonneg
      have hρ'ne : (ρ' : ℝ) ≠ 0 := by linarith
      have hpow_eq : (r / ρ') ^ n * ρ' ^ n = r ^ n := by
        have hρ'pow_ne : (ρ' ^ n : ℝ) ≠ 0 := by
          exact pow_ne_zero _ hρ'ne
        calc
          (r / ρ') ^ n * ρ' ^ n = (r ^ n / ρ' ^ n) * ρ' ^ n := by
            simp [div_pow]
          _ = r ^ n := by
            field_simp [hρ'pow_ne]
      have hle_q'' : (Nat.succ n : ℝ) * r ^ n ≤ ρ' * ρ' ^ n := by
        simpa [hpow_eq, mul_assoc] using hle_q'
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hle_q''
    have hnorm :
        ‖derivTerm n x‖ =
          (Nat.succ n : ℝ) * |c (Nat.succ n)| * |x - a| ^ n := by
      calc
        ‖derivTerm n x‖ =
            ‖(Nat.succ n : ℝ) * c (Nat.succ n)‖ * ‖(x - a) ^ n‖ := by
              simp [derivTerm, norm_mul, mul_assoc]
        _ = ‖(Nat.succ n : ℝ)‖ * ‖c (Nat.succ n)‖ * ‖(x - a) ^ n‖ := by
              simp [norm_mul, mul_comm]
        _ = (Nat.succ n : ℝ) * |c (Nat.succ n)| * |x - a| ^ n := by
              calc
                ‖(Nat.succ n : ℝ)‖ * ‖c (Nat.succ n)‖ * ‖(x - a) ^ n‖
                    = |(Nat.succ n : ℝ)| * ‖c (Nat.succ n)‖ * ‖(x - a) ^ n‖ := by
                      rw [Real.norm_eq_abs]
                _ = (Nat.succ n : ℝ) * ‖c (Nat.succ n)‖ * ‖(x - a) ^ n‖ := by
                      rw [abs_nat_succ_real]
                _ = (Nat.succ n : ℝ) * |c (Nat.succ n)| * ‖(x - a) ^ n‖ := by
                      rw [Real.norm_eq_abs]
                _ = (Nat.succ n : ℝ) * |c (Nat.succ n)| * |x - a| ^ n := by
                      rw [norm_pow, Real.norm_eq_abs]
    calc
      ‖derivTerm n x‖
          = (Nat.succ n : ℝ) * |c (Nat.succ n)| * |x - a| ^ n := hnorm
      _ ≤ (Nat.succ n : ℝ) * |c (Nat.succ n)| * r ^ n := by
        have hnonneg' : 0 ≤ (Nat.succ n : ℝ) * |c (Nat.succ n)| := by
          exact mul_nonneg (by exact_mod_cast (Nat.zero_le (Nat.succ n))) (abs_nonneg _)
        exact mul_le_mul_of_nonneg_left hpow hnonneg'
      _ = |c (Nat.succ n)| * ((Nat.succ n : ℝ) * r ^ n) := by
        ring
      _ ≤ |c (Nat.succ n)| * ρ' ^ (Nat.succ n) := by
        exact mul_le_mul_of_nonneg_left hle_r (abs_nonneg _)
  have hunif_deriv :
      TendstoUniformlyOn partialDeriv g atTop (Set.Icc (a - r) (a + r)) := by
    simpa [partialDeriv, g] using
      (tendstoUniformlyOn_tsum_nat_eventually
        (f := fun n x => derivTerm n x)
        (u := fun n => |c (Nat.succ n)| * ρ' ^ (Nat.succ n))
        hsum_u hterm_bound)
  have h_unique : UniqueDiffOn ℝ (Set.Icc (a - r) (a + r)) :=
    uniqueDiffOn_Icc (by linarith [hrpos])
  have sum_range_succ_shift (f : ℕ → ℝ) (h0 : f 0 = 0) :
      ∀ N,
        Finset.sum (Finset.range (Nat.succ N)) (fun n => f n) =
          Finset.sum (Finset.range N) (fun n => f (Nat.succ n)) := by
    intro N
    induction N with
    | zero =>
        simp [h0]
    | succ N ih =>
        simp [Finset.sum_range_succ, ih, add_comm, add_left_comm]
  have hderiv_term :
      ∀ n x, x ∈ Set.Icc (a - r) (a + r) →
        derivWithin (fun y : ℝ => c n * (y - a) ^ n) (Set.Icc (a - r) (a + r)) x =
          (n : ℝ) * c n * (x - a) ^ (n - 1) := by
    intro n x hx
    have hdiff_sub :
        DifferentiableWithinAt ℝ (fun y : ℝ => y - a) (Set.Icc (a - r) (a + r)) x := by
      have hdiff_at : DifferentiableAt ℝ (fun y : ℝ => y - a) x := by
        fun_prop
      exact hdiff_at.differentiableWithinAt
    have hdiff_pow :
        DifferentiableWithinAt ℝ (fun y : ℝ => (y - a) ^ n) (Set.Icc (a - r) (a + r)) x := by
      simpa using hdiff_sub.pow n
    have hderiv_sub :
        derivWithin (fun y : ℝ => y - a) (Set.Icc (a - r) (a + r)) x = 1 := by
      have hunique : UniqueDiffWithinAt ℝ (Set.Icc (a - r) (a + r)) x := h_unique x hx
      calc
        derivWithin (fun y : ℝ => y - a) (Set.Icc (a - r) (a + r)) x
            = derivWithin (fun y : ℝ => y) (Set.Icc (a - r) (a + r)) x := by
              simp [derivWithin_sub_const]
        _ = 1 := by
              exact derivWithin_id' (𝕜 := ℝ) (s := Set.Icc (a - r) (a + r)) (x := x) hunique
    have hderiv_pow :
        derivWithin (fun y : ℝ => (y - a) ^ n) (Set.Icc (a - r) (a + r)) x =
          (n : ℝ) * (x - a) ^ (n - 1) * 1 := by
      simpa [hderiv_sub] using
        (derivWithin_fun_pow (f := fun y : ℝ => y - a)
          (s := Set.Icc (a - r) (a + r)) (x := x) (n := n) hdiff_sub)
    have hderiv_const :
        derivWithin (fun y : ℝ => c n * (y - a) ^ n) (Set.Icc (a - r) (a + r)) x =
          c n * derivWithin (fun y : ℝ => (y - a) ^ n) (Set.Icc (a - r) (a + r)) x := by
      simpa using
        (derivWithin_const_mul (c := c n) (d := fun y : ℝ => (y - a) ^ n)
          (s := Set.Icc (a - r) (a + r)) (x := x) hdiff_pow)
    calc
      derivWithin (fun y : ℝ => c n * (y - a) ^ n) (Set.Icc (a - r) (a + r)) x
          = c n * derivWithin (fun y : ℝ => (y - a) ^ n) (Set.Icc (a - r) (a + r)) x :=
            hderiv_const
      _ = c n * ((n : ℝ) * (x - a) ^ (n - 1) * 1) := by
            simp [hderiv_pow]
      _ = (n : ℝ) * c n * (x - a) ^ (n - 1) := by
            ring
  have hderiv_partialSum :
      ∀ N x, x ∈ Set.Icc (a - r) (a + r) →
        derivWithin (fun y : ℝ => fSeq N y) (Set.Icc (a - r) (a + r)) x =
          partialDeriv N x := by
    intro N x hx
    have hdiff_term :
        ∀ n ∈ Finset.range (Nat.succ N),
          DifferentiableWithinAt ℝ (fun y : ℝ => c n * (y - a) ^ n)
          (Set.Icc (a - r) (a + r)) x := by
      intro n hn
      have hdiff : DifferentiableAt ℝ (fun y : ℝ => c n * (y - a) ^ n) x := by
        fun_prop
      exact hdiff.differentiableWithinAt
    have hsum :
        derivWithin (fun y : ℝ => fSeq N y) (Set.Icc (a - r) (a + r)) x =
          Finset.sum (Finset.range (Nat.succ N))
            (fun n =>
              derivWithin (fun y : ℝ => c n * (y - a) ^ n)
                (Set.Icc (a - r) (a + r)) x) := by
      simpa [fSeq, partialSum, Finset.sum_fn] using
        (derivWithin_sum (u := Finset.range (Nat.succ N))
          (A := fun n y => c n * (y - a) ^ n) (s := Set.Icc (a - r) (a + r))
          (x := x) hdiff_term)
    have hsum' :
        Finset.sum (Finset.range (Nat.succ N))
          (fun n =>
            derivWithin (fun y : ℝ => c n * (y - a) ^ n)
              (Set.Icc (a - r) (a + r)) x)
        = Finset.sum (Finset.range (Nat.succ N))
            (fun n => (n : ℝ) * c n * (x - a) ^ (n - 1)) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      exact hderiv_term n x hx
    have hshift :
        Finset.sum (Finset.range (Nat.succ N))
          (fun n => (n : ℝ) * c n * (x - a) ^ (n - 1)) =
          Finset.sum (Finset.range N)
            (fun n => (Nat.succ n : ℝ) * c (Nat.succ n) * (x - a) ^ n) := by
      simpa [Nat.succ_sub_one, mul_comm, mul_left_comm, mul_assoc] using
        (sum_range_succ_shift (f := fun n =>
          (n : ℝ) * c n * (x - a) ^ (n - 1)) (h0 := by simp) N)
    calc
      derivWithin (fun y : ℝ => fSeq N y) (Set.Icc (a - r) (a + r)) x
          = Finset.sum (Finset.range (Nat.succ N))
              (fun n =>
                derivWithin (fun y : ℝ => c n * (y - a) ^ n)
                  (Set.Icc (a - r) (a + r)) x) := hsum
      _ = Finset.sum (Finset.range (Nat.succ N))
            (fun n => (n : ℝ) * c n * (x - a) ^ (n - 1)) := hsum'
      _ = Finset.sum (Finset.range N)
            (fun n => (Nat.succ n : ℝ) * c (Nat.succ n) * (x - a) ^ n) := hshift
      _ = partialDeriv N x := by
        simp [partialDeriv, derivTerm]
  have hderiv :
      TendstoUniformlyOn
        (fun n x => derivWithin (fSeq n) (Set.Icc (a - r) (a + r)) x) g
        atTop (Set.Icc (a - r) (a + r)) := by
    refine hunif_deriv.congr ?_
    refine Filter.univ_mem' ?_
    intro n
    intro x hx
    exact (hderiv_partialSum n x hx).symm
  have hcont : ∀ N, ContDiffOn ℝ 1 (fSeq N) (Set.Icc (a - r) (a + r)) := by
    intro N
    classical
    have hterm :
        ∀ n ∈ Finset.range (Nat.succ N),
          ContDiffOn ℝ 1 (fun x : ℝ => c n * (x - a) ^ n) (Set.Icc (a - r) (a + r)) := by
      intro n hn
      have hcont' : ContDiff ℝ 1 (fun x : ℝ => c n * (x - a) ^ n) := by
        fun_prop
      exact hcont'.contDiffOn
    simpa [fSeq, partialSum] using
      (ContDiffOn.sum (s := Finset.range (Nat.succ N)) (t := Set.Icc (a - r) (a + r))
        (f := fun n : ℕ => fun x : ℝ => c n * (x - a) ^ n) hterm)
  have hval : ∃ l, Tendsto (fun n => fSeq n a) atTop (𝓝 l) := by
    refine ⟨c 0, ?_⟩
    have hconst : ∀ n : ℕ, fSeq n a = c 0 := by
      intro n
      induction n with
      | zero =>
          simp [fSeq, partialSum]
      | succ n ih =>
          calc
            fSeq (Nat.succ n) a =
                fSeq n a + c (Nat.succ n) * 0 ^ (Nat.succ n) := by
                  simp [fSeq, partialSum, Finset.sum_range_succ]
            _ = c 0 := by
                  simp [ih]
    have hconst' : (fun n => fSeq n a) = fun _ => c 0 := by
      funext n
      exact hconst n
    simp [hconst']
  have hc : a ∈ Set.Icc (a - r) (a + r) := by
    constructor <;> linarith [le_of_lt hrpos]
  obtain ⟨f, hf_contDiff, hf_tendsto, hf_deriv⟩ :=
    uniform_limit_of_uniform_deriv
      (a := a - r) (b := a + r) (fSeq := fSeq) (g := g) (c := a)
      hcont hderiv hc hval
  have hlim_sum :
      ∀ y ∈ Set.Icc (a - r) (a + r),
        Tendsto (fun N => fSeq N y) atTop
          (𝓝 (tsum fun n => c n * (y - a) ^ n)) := by
    intro y hy
    have hlim0 :
        Tendsto (fun N => partialSum N y) atTop
          (𝓝 (tsum fun n => c n * (y - a) ^ n)) := hunif.tendsto_at hy
    have hshift :
        Tendsto (fun N => partialSum (Nat.succ N) y) atTop
          (𝓝 (tsum fun n => c n * (y - a) ^ n)) := by
      simpa [Nat.succ_eq_add_one] using hlim0.comp (tendsto_add_atTop_nat 1)
    simpa [fSeq] using hshift
  have hf_eq :
      ∀ y ∈ Set.Icc (a - r) (a + r),
        f y = tsum fun n => c n * (y - a) ^ n := by
    intro y hy
    have hlim_f : Tendsto (fun N => fSeq N y) atTop (𝓝 (f y)) := hf_tendsto.tendsto_at hy
    have hlim_sum' := hlim_sum y hy
    exact tendsto_nhds_unique hlim_f hlim_sum'
  have htsum_contDiff :
      ContDiffOn ℝ 1 (fun y => tsum fun n => c n * (y - a) ^ n)
        (Set.Icc (a - r) (a + r)) := by
    have hEq : ∀ y ∈ Set.Icc (a - r) (a + r),
        f y = tsum fun n => c n * (y - a) ^ n := hf_eq
    exact
      (contDiffOn_congr (f₁ := f)
        (f := fun y => tsum fun n => c n * (y - a) ^ n)
        (s := Set.Icc (a - r) (a + r)) hEq).1 hf_contDiff
  have hxIcc : x ∈ Set.Icc (a - r) (a + r) := by
    have hx1 : a - r < x := by
      have hx1' : -r < x - a := (abs_lt.mp hrx).1
      linarith
    have hx2 : x < a + r := by
      have hx2' : x - a < r := (abs_lt.mp hrx).2
      linarith
    exact ⟨le_of_lt hx1, le_of_lt hx2⟩
  have hxlt : a - r < x := by
    have hx1' : -r < x - a := (abs_lt.mp hrx).1
    linarith
  have hxgt : x < a + r := by
    have hx2' : x - a < r := (abs_lt.mp hrx).2
    linarith
  have hnhds : Set.Icc (a - r) (a + r) ∈ 𝓝 x := Icc_mem_nhds hxlt hxgt
  have hdiff_tsum :
      DifferentiableAt ℝ (fun y : ℝ => tsum fun n => c n * (y - a) ^ n) x := by
    have hdiff_on :
        DifferentiableOn ℝ (fun y : ℝ => tsum fun n => c n * (y - a) ^ n)
          (Set.Icc (a - r) (a + r)) := by
        simpa using (htsum_contDiff.differentiableOn (by exact le_rfl))
    have hdiff_within :
        DifferentiableWithinAt ℝ (fun y : ℝ => tsum fun n => c n * (y - a) ^ n)
          (Set.Icc (a - r) (a + r)) x := hdiff_on x hxIcc
    exact hdiff_within.differentiableAt hnhds
  have hderivWithin_tsum :
      derivWithin (fun y : ℝ => tsum fun n => c n * (y - a) ^ n)
        (Set.Icc (a - r) (a + r)) x = g x := by
    have hEqOn :
        Set.EqOn f (fun y : ℝ => tsum fun n => c n * (y - a) ^ n)
          (Set.Icc (a - r) (a + r)) := by
      intro y hy
      exact hf_eq y hy
    have hcongr :
        derivWithin (fun y : ℝ => tsum fun n => c n * (y - a) ^ n)
          (Set.Icc (a - r) (a + r)) x =
        derivWithin f (Set.Icc (a - r) (a + r)) x := by
      simpa using
        (derivWithin_congr (s := Set.Icc (a - r) (a + r))
          (f₁ := f) (f := fun y : ℝ => tsum fun n => c n * (y - a) ^ n) hEqOn
          (hEqOn hxIcc)).symm
    calc
      derivWithin (fun y : ℝ => tsum fun n => c n * (y - a) ^ n)
          (Set.Icc (a - r) (a + r)) x
          = derivWithin f (Set.Icc (a - r) (a + r)) x := hcongr
      _ = g x := hf_deriv x hxIcc
  have hunique : UniqueDiffWithinAt ℝ (Set.Icc (a - r) (a + r)) x := h_unique x hxIcc
  have hderiv_tsum :
      deriv (fun y : ℝ => tsum fun n => c n * (y - a) ^ n) x = g x := by
    have h_eq :
        derivWithin (fun y : ℝ => tsum fun n => c n * (y - a) ^ n)
          (Set.Icc (a - r) (a + r)) x =
        deriv (fun y : ℝ => tsum fun n => c n * (y - a) ^ n) x := by
      simpa using
        (derivWithin_of_mem_nhds (f := fun y : ℝ => tsum fun n => c n * (y - a) ^ n)
          (s := Set.Icc (a - r) (a + r)) (x := x) hnhds)
    calc
      deriv (fun y : ℝ => tsum fun n => c n * (y - a) ^ n) x
          = derivWithin (fun y : ℝ => tsum fun n => c n * (y - a) ^ n)
              (Set.Icc (a - r) (a + r)) x := by
                symm
                exact h_eq
      _ = g x := hderivWithin_tsum
  have hsum_deriv : Summable (fun n => derivTerm n x) := by
    have hbound_x :
        ∀ᶠ n in atTop, ‖derivTerm n x‖ ≤ |c (Nat.succ n)| * ρ' ^ (Nat.succ n) := by
      exact hterm_bound.mono (fun n hn => hn x hxIcc)
    exact Summable.of_norm_bounded_eventually_nat hsum_u hbound_x
  refine ⟨hdiff_tsum, ?_, ?_⟩
  · simpa [g, derivTerm] using hderiv_tsum
  · simpa [derivTerm] using hsum_deriv

/-- Example 6.2.14: The power series `∑ x^n / n!` has infinite radius of
convergence, so it defines a function `f(x) = ∑ x^n / n!` on all real
numbers.  It satisfies `f(0) = 1`, differentiates term by term to give
`f' = f`, and coincides with the usual exponential function. -/
def example6_2_14_series (x : ℝ) : ℝ :=
  ∑' n : ℕ, x ^ n / (Nat.factorial n)

lemma example6_2_14_summable (x : ℝ) :
    Summable fun n : ℕ => x ^ n / (Nat.factorial n) := by
  simpa using (Real.summable_pow_div_factorial x)

@[simp] lemma example6_2_14_series_zero : example6_2_14_series 0 = 1 := by
  have hzero : ∀ n : ℕ, n ≠ 0 → (0 : ℝ) ^ n / (Nat.factorial n) = 0 := by
    intro n hn
    cases n with
    | zero => cases (hn rfl)
    | succ n =>
        simp
  calc
    example6_2_14_series 0 = ∑' n : ℕ, (0 : ℝ) ^ n / (Nat.factorial n) := rfl
    _ = (0 : ℝ) ^ 0 / (Nat.factorial 0) := by
          exact (tsum_eq_single (L := SummationFilter.unconditional ℕ) 0
            (by intro n hn; exact hzero n hn))
    _ = 1 := by
          simp

lemma example6_2_14_deriv (x : ℝ) :
    HasDerivAt example6_2_14_series (example6_2_14_series x) x := by
  classical
  let c : ℕ → ℝ := fun n => 1 / (Nat.factorial n)
  let ρ : ℝ := |x| + 1
  have hconv :
      ∀ y ∈ Set.Ioo (0 - ρ) (0 + ρ), Summable fun n => c n * (y - 0) ^ n := by
    intro y _hy
    simpa [c, div_eq_mul_inv, mul_comm] using
      (example6_2_14_summable y)
  have hxIoo : x ∈ Set.Ioo (0 - ρ) (0 + ρ) := by
    have hxabs : |x| < ρ := by
      dsimp [ρ]
      linarith
    simpa using (abs_lt.mp hxabs)
  obtain ⟨hdiff, hderiv, _hsum⟩ :=
    deriv_powerSeries_eq_series (a := (0 : ℝ)) (ρ := ρ) (c := c) hconv x hxIoo
  have hcoeff :
      ∀ n : ℕ,
        (Nat.succ n : ℝ) * c (Nat.succ n) = 1 / (Nat.factorial n) := by
    intro n
    have hne : (Nat.succ n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero n)
    calc
      (Nat.succ n : ℝ) * c (Nat.succ n)
          = (Nat.succ n : ℝ) * (1 / (Nat.factorial (Nat.succ n))) := by
              simp [c]
      _ = (Nat.succ n : ℝ) / ((Nat.succ n : ℝ) * (Nat.factorial n)) := by
              simp [Nat.factorial_succ, div_eq_mul_inv]
      _ = 1 / (Nat.factorial n) := by
              field_simp [hne]
  have hderiv' :
      deriv (fun y : ℝ => tsum fun n => c n * (y - 0) ^ n) x =
        example6_2_14_series x := by
    calc
      deriv (fun y : ℝ => tsum fun n => c n * (y - 0) ^ n) x
          = tsum fun n => (Nat.succ n : ℝ) * c (Nat.succ n) * (x - 0) ^ n := by
            simpa using hderiv
      _ = tsum fun n => (1 / (Nat.factorial n)) * x ^ n := by
            refine tsum_congr ?_
            intro n
            calc
              (Nat.succ n : ℝ) * c (Nat.succ n) * (x - 0) ^ n
                  = (Nat.succ n : ℝ) * c (Nat.succ n) * x ^ n := by
                      simp
              _ = (1 / (Nat.factorial n)) * x ^ n := by
                      rw [hcoeff n]
      _ = tsum fun n => x ^ n / (Nat.factorial n) := by
            refine tsum_congr ?_
            intro n
            simp [div_eq_mul_inv, mul_comm]
      _ = example6_2_14_series x := by
            rfl
  have hHas :
      HasDerivAt (fun y : ℝ => tsum fun n => c n * y ^ n)
        (example6_2_14_series x) x := by
    simpa using (hdiff.hasDerivAt.congr_deriv hderiv')
  have hfun :
      (fun y : ℝ => tsum fun n => c n * y ^ n) = example6_2_14_series := by
    funext y
    refine tsum_congr ?_
    intro n
    simp [c, div_eq_mul_inv, mul_comm]
  simpa [hfun] using hHas

lemma example6_2_14_series_eq_real_exp (x : ℝ) :
    example6_2_14_series x = Real.exp x := by
  have h_exp := congrArg (fun f => f x) (Real.exp_eq_exp_ℝ)
  have h_series :=
    congrArg (fun f => f x) (NormedSpace.exp_eq_tsum_div (𝕂 := ℝ) (𝔸 := ℝ))
  calc
    example6_2_14_series x = ∑' n : ℕ, x ^ n / (Nat.factorial n) := rfl
    _ = (NormedSpace.exp ℝ) x := by
          simpa using h_series.symm
    _ = Real.exp x := by
          simpa using h_exp.symm

/-- Example 6.2.15: For `x ∈ (-1, 1)`, the series `∑_{n=1}^∞ n x^n` converges
to `x / (1 - x)^2`, obtained by differentiating the geometric series and
multiplying by `x`. -/
lemma example6_2_15_series_closed_form {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (∑' n : ℕ, (Nat.succ n : ℝ) * x ^ (Nat.succ n)) = x / (1 - x) ^ 2 := by
  have hx' : -1 < x ∧ x < 1 := by simpa using hx
  have hxabs : |x| < 1 := abs_lt.mpr hx'
  have hr : ‖x‖ < 1 := by simpa [Real.norm_eq_abs] using hxabs
  have hsum_geom : Summable (fun n : ℕ => x ^ n) :=
    summable_geometric_of_abs_lt_one (by simpa using hxabs)
  have hsum_n_mul : Summable (fun n : ℕ => (n : ℝ) * x ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
          (r := x) hr).summable
  have htsum_nplus :
      tsum (fun n : ℕ => ((n + 1 : ℝ) * x ^ n)) = 1 / (1 - x) ^ 2 := by
    have htsum_add := hsum_n_mul.hasSum.add hsum_geom.hasSum
    have hfun :
        (fun n : ℕ => ((n + 1 : ℝ) * x ^ n)) =
          fun n : ℕ => (n : ℝ) * x ^ n + x ^ n := by
      funext n; ring
    have htsum_add' :
        tsum (fun n : ℕ => (n : ℝ) * x ^ n + x ^ n) =
          tsum (fun n : ℕ => (n : ℝ) * x ^ n) +
            tsum (fun n : ℕ => x ^ n) := htsum_add.tsum_eq
    have htsum_n_mul :
        tsum (fun n : ℕ => (n : ℝ) * x ^ n) = x / (1 - x) ^ 2 := by
      simpa using
        (tsum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
          (r := x) hr)
    have htsum_geom :
        tsum (fun n : ℕ => x ^ n) = 1 / (1 - x) := by
      simpa using
        (tsum_geometric_of_abs_lt_one (r := x) (by simpa using hxabs))
    have hx1 : (1 - x) ≠ 0 := by
      have hxlt : x < 1 := hx'.2
      linarith
    have hfrac : (1 : ℝ) / (1 - x) = (1 - x) / (1 - x) ^ 2 := by
      field_simp [hx1]
    calc
      tsum (fun n : ℕ => ((n + 1 : ℝ) * x ^ n))
          = tsum (fun n : ℕ => (n : ℝ) * x ^ n + x ^ n) := by
              simp [hfun]
      _ = tsum (fun n : ℕ => (n : ℝ) * x ^ n) +
            tsum (fun n : ℕ => x ^ n) := htsum_add'
      _ = x / (1 - x) ^ 2 + 1 / (1 - x) := by
            simp [htsum_n_mul, htsum_geom]
      _ = 1 / (1 - x) ^ 2 := by
            calc
              x / (1 - x) ^ 2 + 1 / (1 - x)
                  = x / (1 - x) ^ 2 + (1 - x) / (1 - x) ^ 2 := by
                      simp [hfrac]
              _ = (x + (1 - x)) / (1 - x) ^ 2 := by ring
              _ = 1 / (1 - x) ^ 2 := by ring
  have hfun :
      (fun n : ℕ => (Nat.succ n : ℝ) * x ^ (Nat.succ n)) =
        fun n : ℕ => x * ((n + 1 : ℝ) * x ^ n) := by
    funext n
    calc
      (Nat.succ n : ℝ) * x ^ (Nat.succ n)
          = (n + 1 : ℝ) * (x ^ n * x) := by
              simp [Nat.succ_eq_add_one, pow_succ]
      _ = x * ((n + 1 : ℝ) * x ^ n) := by ring
  have htsum_mul :
      tsum (fun n : ℕ => x * ((n + 1 : ℝ) * x ^ n)) =
        x * tsum (fun n : ℕ => ((n + 1 : ℝ) * x ^ n)) := by
    simpa using
      (tsum_mul_left (a := x) (f := fun n : ℕ => ((n + 1 : ℝ) * x ^ n)))
  calc
    (∑' n : ℕ, (Nat.succ n : ℝ) * x ^ (Nat.succ n))
        = tsum (fun n : ℕ => x * ((n + 1 : ℝ) * x ^ n)) := by
            refine tsum_congr ?_
            intro n
            exact congrArg (fun f => f n) hfun
    _ = x * tsum (fun n : ℕ => ((n + 1 : ℝ) * x ^ n)) := htsum_mul
    _ = x * (1 / (1 - x) ^ 2) := by simp [htsum_nplus]
    _ = x / (1 - x) ^ 2 := by simp [div_eq_mul_inv]

end
end Section02
end Chap06
