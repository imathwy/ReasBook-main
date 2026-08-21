/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import Mathlib

section Chap05
section Section05

open Set Filter Real
open BigOperators
open scoped BigOperators

/-- Definition 5.5.1. For a function `f : [a, b) → ℝ` that is Riemann integrable
on every `[a, c]` with `c < b`, we define `∫ a^b f` as the limit
`lim_{c → b⁻} ∫ a^c f` when it exists. For `f : [a, ∞) → ℝ`, integrable on
every `[a, c]`, we define `∫ a^∞ f` as `lim_{c → ∞} ∫ a^c f`. The improper
integral converges if the relevant limit exists and diverges otherwise. The
analogous definitions for a left-hand endpoint are similar. -/
def ImproperIntegralRight (f : ℝ → ℝ) (a b l : ℝ) : Prop :=
  (∀ c, c < b → MeasureTheory.IntegrableOn f (Set.Icc a c)) ∧
    Tendsto (fun c : ℝ => ∫ x in a..c, f x) (nhdsWithin b (Set.Iio b)) (nhds l)

/-- Improper integral over `[a, ∞)` converging to `l`. -/
def ImproperIntegralAtTop (f : ℝ → ℝ) (a l : ℝ) : Prop :=
  (∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c)) ∧
    Tendsto (fun c : ℝ => ∫ x in a..c, f x) atTop (nhds l)

/-- Convergence of an improper integral on `[a, b)`. -/
def ImproperIntegralRightConverges (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ l, ImproperIntegralRight f a b l

/-- Convergence of an improper integral on `[a, ∞)`. -/
def ImproperIntegralAtTopConverges (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ l, ImproperIntegralAtTop f a l

/-- Helper: `x ↦ 1 / x^p` is integrable on any interval `[1, c]`. -/
lemma integrableOn_Icc_one_div_rpow (p c : ℝ) :
    MeasureTheory.IntegrableOn (fun x : ℝ => 1 / x ^ p) (Set.Icc (1 : ℝ) c) := by
  by_cases h : (1 : ℝ) ≤ c
  · have hc : 0 < c := lt_of_lt_of_le zero_lt_one h
    have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) c := Set.notMem_uIcc_of_lt zero_lt_one hc
    have hInt :
        IntervalIntegrable (fun x : ℝ => x ^ (-p)) MeasureTheory.volume (1 : ℝ) c := by
      simpa using
        (intervalIntegral.intervalIntegrable_rpow (μ := MeasureTheory.volume) (a := (1 : ℝ))
          (b := c) (r := -p) (Or.inr h0))
    have hIntOn :
        MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-p)) (Set.Icc (1 : ℝ) c) := by
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) h
        (ha := by simp)).mp hInt
    have hEq : EqOn (fun x : ℝ => 1 / x ^ p) (fun x : ℝ => x ^ (-p)) (Set.Icc (1 : ℝ) c) := by
      intro x hx
      have hx0 : 0 ≤ x := by linarith [hx.1]
      calc
        1 / x ^ p = (x ^ p)⁻¹ := by simp [one_div]
        _ = x ^ (-p) := by simpa using (Real.rpow_neg hx0 p).symm
    exact (MeasureTheory.integrableOn_congr_fun hEq measurableSet_Icc).2 hIntOn
  · have hc : c < (1 : ℝ) := lt_of_not_ge h
    have hcc : Set.Icc (1 : ℝ) c = ∅ := Set.Icc_eq_empty_of_lt hc
    simp [hcc]

/-- Helper: explicit interval integral for `x ↦ 1 / x^p` on positive bounds. -/
lemma improperIntegral_p_test_integral_formula {a b p : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hp : p ≠ 1) :
    ∫ x in a..b, 1 / x ^ p = (b ^ (1 - p) - a ^ (1 - p)) / (1 - p) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := Set.notMem_uIcc_of_lt ha hb
  have hEq : EqOn (fun x : ℝ => 1 / x ^ p) (fun x : ℝ => x ^ (-p)) (Set.uIcc a b) := by
    intro x hx
    have hx0 : 0 ≤ x := by
      have hmin : 0 ≤ min a b := le_min (le_of_lt ha) (le_of_lt hb)
      have hx' : min a b ≤ x := by
        rcases Set.mem_uIcc.mp hx with hx' | hx'
        · exact (min_le_left _ _).trans hx'.1
        · exact (min_le_right _ _).trans hx'.1
      exact le_trans hmin hx'
    calc
      1 / x ^ p = (x ^ p)⁻¹ := by simp [one_div]
      _ = x ^ (-p) := by simpa using (Real.rpow_neg hx0 p).symm
  have hIntegral :
      ∫ x in a..b, 1 / x ^ p = ∫ x in a..b, x ^ (-p) := by
    simpa using (intervalIntegral.integral_congr (μ := MeasureTheory.volume) hEq)
  have hRpow :
      ∫ x in a..b, x ^ (-p) = (b ^ ((-p) + 1) - a ^ ((-p) + 1)) / ((-p) + 1) := by
    have hcond : (-1 : ℝ) < -p ∨ (-p ≠ -1 ∧ (0 : ℝ) ∉ Set.uIcc a b) := by
      right
      refine ⟨?_, h0⟩
      intro hpneg
      apply hp
      linarith [hpneg]
    simpa using (integral_rpow (a := a) (b := b) (r := -p) hcond)
  calc
    ∫ x in a..b, 1 / x ^ p = ∫ x in a..b, x ^ (-p) := hIntegral
    _ = (b ^ ((-p) + 1) - a ^ ((-p) + 1)) / ((-p) + 1) := hRpow
    _ = (b ^ (1 - p) - a ^ (1 - p)) / (1 - p) := by
      simp [sub_eq_add_neg, add_comm]

/-- Proposition 5.5.2 (`p`-test for integrals). The improper integral
`∫₁^∞ x^{-p}` converges to `1 / (p - 1)` for `p > 1` and diverges for
`0 < p ≤ 1`. The improper integral `∫₀^1 x^{-p}` converges to
`1 / (1 - p)` for `0 < p < 1` and diverges for `p ≥ 1`. -/
theorem improperIntegral_p_test (p : ℝ) :
    (p > 1 → ImproperIntegralAtTop (fun x : ℝ => 1 / x ^ p) 1 (1 / (p - 1))) ∧
      (0 < p → p ≤ 1 → ¬ ImproperIntegralAtTopConverges (fun x : ℝ => 1 / x ^ p) 1) ∧
      (0 < p → p < 1 →
        Tendsto (fun c : ℝ => ∫ x in c..(1 : ℝ), 1 / x ^ p)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / (1 - p)))) ∧
      (p ≥ 1 → ¬ ∃ l : ℝ,
        Tendsto (fun c : ℝ => ∫ x in c..(1 : ℝ), 1 / x ^ p)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds l)) :=
by
  refine ⟨?h1, ?h2, ?h3, ?h4⟩
  · intro hp1
    refine ⟨?hInt, ?hTend⟩
    · intro c
      exact integrableOn_Icc_one_div_rpow p c
    · have hpne : p ≠ 1 := by linarith
      have hEq :
          (fun c : ℝ => ∫ x in 1..c, 1 / x ^ p) =ᶠ[atTop]
            fun c => (c ^ (1 - p) - 1) / (1 - p) := by
        refine (eventuallyEq_of_mem (Ioi_mem_atTop 0) ?_)
        intro c hc
        simpa using
          (improperIntegral_p_test_integral_formula (a := (1 : ℝ)) (b := c) (p := p)
            zero_lt_one hc hpne)
      have hpow : Tendsto (fun c : ℝ => c ^ (1 - p)) atTop (nhds 0) := by
        have hpos : 0 < p - 1 := by linarith
        have hpow' : Tendsto (fun c : ℝ => c ^ (-(p - 1))) atTop (nhds 0) :=
          tendsto_rpow_neg_atTop hpos
        simpa [neg_sub] using hpow'
      have hsub : Tendsto (fun c : ℝ => c ^ (1 - p) - 1) atTop (nhds (-1)) := by
        simpa using (hpow.sub tendsto_const_nhds)
      have hdiv :
          Tendsto (fun c : ℝ => (c ^ (1 - p) - 1) / (1 - p)) atTop
            (nhds (-1 / (1 - p))) :=
        hsub.div_const (1 - p)
      have hval : (-1 : ℝ) / (1 - p) = 1 / (p - 1) := by
        have hden : (1 - p) ≠ 0 := by linarith
        have hden' : (p - 1) ≠ 0 := by linarith
        field_simp [hden, hden']
        ring
      exact (by simpa [hval] using (hdiv.congr' hEq.symm))
  · intro hp0 hp_le
    by_cases h1 : p = 1
    · subst h1
      intro hconv
      rcases hconv with ⟨l, hl⟩
      have hEq :
          (fun c : ℝ => ∫ x in 1..c, 1 / x) =ᶠ[atTop] fun c => Real.log c := by
        refine (eventuallyEq_of_mem (Ioi_mem_atTop 0) ?_)
        intro c hc
        simpa using (integral_one_div_of_pos (a := (1 : ℝ)) (b := c) zero_lt_one hc)
      have hlog :
          Tendsto (fun c : ℝ => ∫ x in 1..c, 1 / x) atTop atTop :=
        (Real.tendsto_log_atTop.congr' hEq.symm)
      exact not_tendsto_nhds_of_tendsto_atTop hlog l (by simpa using hl.2)
    · have hp_lt : p < 1 := lt_of_le_of_ne hp_le h1
      intro hconv
      rcases hconv with ⟨l, hl⟩
      have hEq :
          (fun c : ℝ => ∫ x in 1..c, 1 / x ^ p) =ᶠ[atTop]
            fun c => (c ^ (1 - p) - 1) / (1 - p) := by
        refine (eventuallyEq_of_mem (Ioi_mem_atTop 0) ?_)
        intro c hc
        simpa using
          (improperIntegral_p_test_integral_formula (a := (1 : ℝ)) (b := c) (p := p)
            zero_lt_one hc (by linarith))
      have hpow : Tendsto (fun c : ℝ => c ^ (1 - p)) atTop atTop :=
        tendsto_rpow_atTop (by linarith : 0 < 1 - p)
      have hsub : Tendsto (fun c : ℝ => c ^ (1 - p) - 1) atTop atTop := by
        simpa [sub_eq_add_neg] using
          (tendsto_atTop_add_const_right atTop (-1) hpow)
      have hdiv : Tendsto (fun c : ℝ => (c ^ (1 - p) - 1) / (1 - p)) atTop atTop :=
        (hsub.atTop_div_const (sub_pos.mpr hp_lt))
      have hTend :
          Tendsto (fun c : ℝ => ∫ x in 1..c, 1 / x ^ p) atTop atTop :=
        hdiv.congr' hEq.symm
      exact not_tendsto_nhds_of_tendsto_atTop hTend l hl.2
  · intro hp0 hp_lt
    have hpne : p ≠ 1 := by linarith
    have hEq :
        (fun c : ℝ => ∫ x in c..(1 : ℝ), 1 / x ^ p) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          fun c => (1 - c ^ (1 - p)) / (1 - p) := by
      refine (eventuallyEq_of_mem
        (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0)) ?_)
      intro c hc
      simpa using
        (improperIntegral_p_test_integral_formula (a := c) (b := (1 : ℝ)) (p := p)
          hc zero_lt_one hpne)
    have hpow : Tendsto (fun c : ℝ => c ^ (1 - p)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hpos : 0 < 1 - p := by linarith
      have hpow' :
          Tendsto (fun c : ℝ => (c⁻¹) ^ (p - 1)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have hpow'' :
            Tendsto (fun c : ℝ => (c⁻¹) ^ (-(1 - p))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
          (tendsto_rpow_neg_atTop hpos).comp
            (tendsto_inv_nhdsGT_zero :
              Tendsto (fun x : ℝ => x⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop)
        simpa [neg_sub] using hpow''
      have hEq :
          (fun c : ℝ => (c⁻¹) ^ (p - 1)) = fun c => c ^ (1 - p) := by
        funext c
        calc
          (c⁻¹) ^ (p - 1) = (c⁻¹) ^ (-(1 - p)) := by
            have hExp : p - 1 = -(1 - p) := by ring
            rw [hExp]
          _ = (c⁻¹)⁻¹ ^ (1 - p) := by
            simpa using (Real.rpow_neg_eq_inv_rpow (c⁻¹) (1 - p))
          _ = c ^ (1 - p) := by simp
      simpa [hEq] using hpow'
    have hsub :
        Tendsto (fun c : ℝ => 1 - c ^ (1 - p)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hpow
    have hdiv :
        Tendsto (fun c : ℝ => (1 - c ^ (1 - p)) / (1 - p)) (nhdsWithin 0 (Set.Ioi 0))
          (nhds ((1 - 0) / (1 - p))) :=
      hsub.div_const (1 - p)
    have hlim :
        Tendsto (fun c : ℝ => (1 - c ^ (1 - p)) / (1 - p)) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (1 / (1 - p))) := by
      simpa using hdiv
    exact hlim.congr' hEq.symm
  · intro hp_ge
    by_cases h1 : p = 1
    · subst h1
      intro hconv
      rcases hconv with ⟨l, hl⟩
      have hEq :
          (fun c : ℝ => ∫ x in c..(1 : ℝ), 1 / x) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
            fun c => -Real.log c := by
        refine (eventuallyEq_of_mem
          (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0)) ?_)
        intro c hc
        have hlog : ∫ x in c..(1 : ℝ), 1 / x = Real.log (1 / c) := by
          simpa using (integral_one_div_of_pos (a := c) (b := (1 : ℝ)) hc zero_lt_one)
        simpa [one_div, Real.log_inv] using hlog
      have hlog :
          Tendsto (fun c : ℝ => ∫ x in c..(1 : ℝ), 1 / x) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
        (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr' hEq.symm
      exact not_tendsto_nhds_of_tendsto_atTop hlog l (by simpa using hl)
    · have hp_gt : 1 < p := lt_of_le_of_ne hp_ge (Ne.symm h1)
      intro hconv
      rcases hconv with ⟨l, hl⟩
      have hEq :
          (fun c : ℝ => ∫ x in c..(1 : ℝ), 1 / x ^ p) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
            fun c => (1 - c ^ (1 - p)) / (1 - p) := by
        refine (eventuallyEq_of_mem
          (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0)) ?_)
        intro c hc
        simpa using
          (improperIntegral_p_test_integral_formula (a := c) (b := (1 : ℝ)) (p := p)
            hc zero_lt_one (by linarith))
      have hpow :
          Tendsto (fun c : ℝ => c ^ (1 - p)) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
        have hneg : 1 - p < 0 := by linarith
        simpa using (tendsto_rpow_neg_nhdsGT_zero (y := 1 - p) hneg)
      have hsub :
          Tendsto (fun c : ℝ => c ^ (1 - p) - 1) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
        simpa [sub_eq_add_neg] using
          (tendsto_atTop_add_const_right (nhdsWithin 0 (Set.Ioi 0)) (-1) hpow)
      have hdiv :
          Tendsto (fun c : ℝ => (c ^ (1 - p) - 1) / (p - 1)) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
        (hsub.atTop_div_const (sub_pos.mpr hp_gt))
      have hrew :
          (fun c : ℝ => (1 - c ^ (1 - p)) / (1 - p)) = fun c =>
            (c ^ (1 - p) - 1) / (p - 1) := by
        funext c
        have hden : (1 - p) ≠ 0 := by linarith
        have hden' : (p - 1) ≠ 0 := by linarith
        field_simp [hden, hden']
        ring
      have hTend :
          Tendsto (fun c : ℝ => ∫ x in c..(1 : ℝ), 1 / x ^ p) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
        (hdiv.congr' (by simpa [hrew] using hEq.symm))
      exact not_tendsto_nhds_of_tendsto_atTop hTend l hl

/- Helper: extend local integrability on `(a, ∞)` to all right endpoints. -/
lemma integrableOn_Icc_all {f : ℝ → ℝ} {a b : ℝ}
    (hb : b > a) (hInt : ∀ c > a, MeasureTheory.IntegrableOn f (Set.Icc a c)) :
    ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c) := by
  intro c
  by_cases hca : a < c
  · exact hInt c hca
  · have hca' : c ≤ a := le_of_not_gt hca
    have hcb : c ≤ b := le_trans hca' (le_of_lt hb)
    have hIntab : MeasureTheory.IntegrableOn f (Set.Icc a b) := hInt b hb
    exact (MeasureTheory.IntegrableOn.mono_set hIntab (by
      intro x hx
      exact ⟨hx.1, le_trans hx.2 hcb⟩))

/- Helper: for large `c`, the interval integral from `a` to `c` splits at `b`. -/
lemma eventually_eq_integral_split {f : ℝ → ℝ} {a b : ℝ}
    (hb : b > a) (hInt : ∀ c > a, MeasureTheory.IntegrableOn f (Set.Icc a c)) :
    (fun c : ℝ => ∫ x in a..c, f x) =ᶠ[atTop]
      fun c => (∫ x in a..b, f x) + ∫ x in b..c, f x := by
  refine (eventuallyEq_of_mem (Ioi_mem_atTop b) ?_)
  intro c hc
  have hle_ab : a ≤ b := le_of_lt hb
  have hle_bc : b ≤ c := le_of_lt hc
  have hInt_ab :
      IntervalIntegrable f MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hle_ab).2
      (hInt b hb)
  have hInt_ac : MeasureTheory.IntegrableOn f (Set.Icc a c) :=
    hInt c (lt_trans hb hc)
  have hInt_bc :
      IntervalIntegrable f MeasureTheory.volume b c :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hle_bc).2
      (MeasureTheory.IntegrableOn.mono_set hInt_ac (by
        intro x hx
        exact ⟨(le_trans hle_ab hx.1), hx.2⟩))
  simpa using (intervalIntegral.integral_add_adjacent_intervals hInt_ab hInt_bc).symm

/- Helper: convergence of the tail from `b` implies convergence from `a`. -/
lemma improperIntegralAtTop_of_tail {f : ℝ → ℝ} {a b l : ℝ}
    (hb : b > a) (hInt : ∀ c > a, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (hbConv : ImproperIntegralAtTop f b l) :
    ImproperIntegralAtTop f a ((∫ x in a..b, f x) + l) := by
  refine ⟨integrableOn_Icc_all hb hInt, ?_⟩
  have hEq := eventually_eq_integral_split (f := f) (a := a) (b := b) hb hInt
  have hTend :
      Tendsto (fun c : ℝ => (∫ x in a..b, f x) + ∫ x in b..c, f x) atTop
        (nhds ((∫ x in a..b, f x) + l)) :=
    tendsto_const_nhds.add hbConv.2
  exact hTend.congr' hEq.symm

/- Helper: convergence from `a` implies convergence of the tail from `b`. -/
lemma improperIntegralAtTop_tail_of {f : ℝ → ℝ} {a b l : ℝ}
    (hb : b > a) (hInt : ∀ c > a, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (ha : ImproperIntegralAtTop f a l) :
    ImproperIntegralAtTop f b (l - ∫ x in a..b, f x) := by
  refine ⟨?hIntb, ?hTend⟩
  · have hInta : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c) := ha.1
    have hIntab : MeasureTheory.IntegrableOn f (Set.Icc a b) := hInta b
    intro c
    by_cases hbc : b < c
    · have hIntac : MeasureTheory.IntegrableOn f (Set.Icc a c) := hInta c
      exact (MeasureTheory.IntegrableOn.mono_set hIntac (by
        intro x hx
        exact ⟨(le_trans (le_of_lt hb) hx.1), hx.2⟩))
    · have hcb : c ≤ b := le_of_not_gt hbc
      exact (MeasureTheory.IntegrableOn.mono_set hIntab (by
        intro x hx
        exact ⟨(le_trans (le_of_lt hb) hx.1), le_trans hx.2 hcb⟩))
  · have hEq :
        (fun c : ℝ => ∫ x in b..c, f x) =ᶠ[atTop]
          fun c => (∫ x in a..c, f x) - ∫ x in a..b, f x := by
      refine (eventuallyEq_of_mem (Ioi_mem_atTop b) ?_)
      intro c hc
      have hle_ab : a ≤ b := le_of_lt hb
      have hle_bc : b ≤ c := le_of_lt hc
      have hInt_ab :
          IntervalIntegrable f MeasureTheory.volume a b :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hle_ab).2
          (hInt b hb)
      have hInt_ac : MeasureTheory.IntegrableOn f (Set.Icc a c) :=
        hInt c (lt_trans hb hc)
      have hInt_bc :
          IntervalIntegrable f MeasureTheory.volume b c :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hle_bc).2
          (MeasureTheory.IntegrableOn.mono_set hInt_ac (by
            intro x hx
            exact ⟨(le_trans hle_ab hx.1), hx.2⟩))
      have hEq' :
          (∫ x in a..b, f x) + ∫ x in b..c, f x = ∫ x in a..c, f x :=
        intervalIntegral.integral_add_adjacent_intervals hInt_ab hInt_bc
      linarith
    have hTend' :
        Tendsto (fun c : ℝ => (∫ x in a..c, f x) - ∫ x in a..b, f x) atTop
          (nhds (l - ∫ x in a..b, f x)) :=
      ha.2.sub tendsto_const_nhds
    exact hTend'.congr' hEq.symm

/-- Proposition 5.5.3. If `f : [a, ∞) → ℝ` is Riemann integrable on every
`[a, c]` with `c > a`, then for any `b > a` the improper integral `∫ b^∞ f`
converges if and only if `∫ a^∞ f` converges, and in the convergent case
`∫ a^∞ f = ∫ a..b, f + ∫ b^∞ f`. -/
theorem improperIntegral_tail_convergence {f : ℝ → ℝ} {a b : ℝ}
    (hb : b > a) (hInt : ∀ c > a, MeasureTheory.IntegrableOn f (Set.Icc a c)) :
    ImproperIntegralAtTopConverges f b ↔ ImproperIntegralAtTopConverges f a :=
by
  constructor
  · intro hbConv
    rcases hbConv with ⟨l, hl⟩
    refine ⟨(∫ x in a..b, f x) + l, ?_⟩
    exact improperIntegralAtTop_of_tail (f := f) (a := a) (b := b) hb hInt hl
  · intro haConv
    rcases haConv with ⟨l, hl⟩
    refine ⟨l - ∫ x in a..b, f x, ?_⟩
    exact improperIntegralAtTop_tail_of (f := f) (a := a) (b := b) hb hInt hl

/-- Proposition 5.5.3 (value identity). Under the same hypotheses as
`improperIntegral_tail_convergence`, if the improper integrals from `a` and
from `b` both converge, then the value from `a` splits as the sum of the
integral over `[a, b]` and the improper integral from `b` to `∞`. -/
theorem improperIntegral_tail_value {f : ℝ → ℝ} {a b l₁ l₂ : ℝ}
    (hb : b > a) (hInt : ∀ c > a, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (ha : ImproperIntegralAtTop f a l₁) (hbConv : ImproperIntegralAtTop f b l₂) :
    l₁ = (∫ x in a..b, f x) + l₂ :=
by
  have ha' :
      ImproperIntegralAtTop f a ((∫ x in a..b, f x) + l₂) :=
    improperIntegralAtTop_of_tail (f := f) (a := a) (b := b) hb hInt hbConv
  exact tendsto_nhds_unique ha.2 ha'.2

/- Helper: partial integrals are monotone in the upper bound for nonnegative `f`. -/
lemma intervalIntegral_mono_upper {f : ℝ → ℝ} {a s t : ℝ}
    (hInt : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (hpos : ∀ x, a ≤ x → 0 ≤ f x)
    (has : a ≤ s) (hst : s ≤ t) :
    ∫ x in a..s, f x ≤ ∫ x in a..t, f x := by
  have hat : a ≤ t := le_trans has hst
  have hInt_at :
      IntervalIntegrable f MeasureTheory.volume a t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hat).2 (hInt t)
  have hnonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc a t)] f := by
    refine MeasureTheory.ae_restrict_of_forall_mem (μ := MeasureTheory.volume)
      (measurableSet_Ioc) ?_
    intro x hx
    exact hpos x (le_of_lt hx.1)
  simpa using
    (intervalIntegral.integral_mono_interval (a := a) (b := s) (c := a) (d := t)
      (hca := le_rfl) (hab := has) (hbd := hst) hnonneg hInt_at)

/- Helper: `t ↦ ∫ a..max t a f` is monotone. -/
lemma monotone_integral_max {f : ℝ → ℝ} {a : ℝ}
    (hInt : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (hpos : ∀ x, a ≤ x → 0 ≤ f x) :
    Monotone (fun t : ℝ => ∫ x in a..max t a, f x) := by
  intro s t hst
  have has : a ≤ max s a := le_max_right _ _
  have hst' : max s a ≤ max t a := max_le_max hst le_rfl
  exact intervalIntegral_mono_upper (f := f) (a := a)
    (hInt := hInt) (hpos := hpos) has hst'

/- Helper: max-truncated partial integrals tend to the improper integral value. -/
lemma tendsto_integral_max {f : ℝ → ℝ} {a l : ℝ}
    (hconv : ImproperIntegralAtTop f a l) :
    Tendsto (fun t : ℝ => ∫ x in a..max t a, f x) atTop (nhds l) := by
  have hEq :
      (fun t : ℝ => ∫ x in a..max t a, f x) =ᶠ[atTop]
        fun t => ∫ x in a..t, f x := by
    refine (eventuallyEq_of_mem (Ioi_mem_atTop a) ?_)
    intro t ht
    have ht' : a ≤ t := le_of_lt (by simpa using ht)
    simp [max_eq_left ht']
  exact hconv.2.congr' hEq.symm

/- Helper: range of the max-truncated integral matches the image over `t ≥ a`. -/
lemma range_integral_max_eq_image {f : ℝ → ℝ} {a : ℝ} :
    Set.range (fun t : ℝ => ∫ x in a..max t a, f x) =
      (fun t : ℝ => ∫ x in a..t, f x) '' {t : ℝ | a ≤ t} := by
  ext y; constructor
  · rintro ⟨t, rfl⟩
    refine ⟨max t a, ?_, rfl⟩
    exact le_max_right t a
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ?_⟩
    have ht' : a ≤ t := by simpa using ht
    simp [max_eq_left ht']

/- Helper: composing with a sequence tending to `∞` preserves the limit. -/
lemma tendsto_integral_comp_seq {f : ℝ → ℝ} {a l : ℝ} {x : ℕ → ℝ}
    (hconv : ImproperIntegralAtTop f a l) (hx : Tendsto x atTop atTop) :
    Tendsto (fun n => ∫ t in a..x n, f t) atTop (nhds l) :=
  hconv.2.comp hx

/-- Proposition 5.5.4. Let `f : [a, ∞) → ℝ` be nonnegative and Riemann
integrable on every interval `[a, b]` with `b > a`.
(i) If the improper integral `∫ a^∞ f` converges to `l`, then
`l = sup {∫ a..x, f x | x ≥ a}`.
(ii) For any sequence `xₙ → ∞`, the improper integral converges if and only if
`lim_{n → ∞} ∫ a^{xₙ} f` exists, and in that case the two limits agree. -/
theorem improperIntegral_nonneg_sup_and_seq {f : ℝ → ℝ} {a l : ℝ}
    (hInt : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (hpos : ∀ x, a ≤ x → 0 ≤ f x)
    (hconv : ImproperIntegralAtTop f a l) :
    l = sSup ((fun t : ℝ => ∫ x in a..t, f x) '' {t : ℝ | a ≤ t}) ∧
      ∀ x : ℕ → ℝ,
        Tendsto x atTop atTop →
          (ImproperIntegralAtTop f a l ↔
            Tendsto (fun n => ∫ t in a..x n, f t) atTop (nhds l)) :=
by
  let g : ℝ → ℝ := fun t => ∫ x in a..max t a, f x
  have hmono : Monotone g :=
    monotone_integral_max (f := f) (a := a) hInt hpos
  have hTend : Tendsto g atTop (nhds l) :=
    tendsto_integral_max (f := f) (a := a) hconv
  have hIsLUB : IsLUB (Set.range g) l :=
    isLUB_of_tendsto_atTop hmono hTend
  have hRange :
      Set.range g =
        (fun t : ℝ => ∫ x in a..t, f x) '' {t : ℝ | a ≤ t} := by
    simpa [g] using (range_integral_max_eq_image (f := f) (a := a))
  refine ⟨?_, ?_⟩
  · have hne : (Set.range g).Nonempty := ⟨g a, ⟨a, rfl⟩⟩
    simpa [hRange] using (hIsLUB.csSup_eq hne).symm
  · intro x hx
    constructor
    · intro _
      exact tendsto_integral_comp_seq (f := f) (a := a) (l := l) hconv hx
    · intro _
      exact hconv

/- Helper: comparison bound implies `g` is nonnegative on `[a, ∞)`. -/
lemma comparison_nonneg_g {a : ℝ} {f g : ℝ → ℝ}
    (hbound : ∀ x, a ≤ x → |f x| ≤ g x) :
    ∀ x, a ≤ x → 0 ≤ g x := by
  intro x hx
  exact le_trans (abs_nonneg _) (hbound x hx)

/- Helper: difference of partial integrals is the tail integral. -/
lemma integral_diff_eq_interval {a b c : ℝ} {f : ℝ → ℝ}
    (hIntf : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (hb : a ≤ b) (hbc : b ≤ c) :
    (∫ x in a..c, f x) - (∫ x in a..b, f x) = ∫ x in b..c, f x := by
  have hInt_ac : MeasureTheory.IntegrableOn f (Set.Icc a c) := hIntf c
  have hInt_bc : MeasureTheory.IntegrableOn f (Set.Icc b c) := by
    refine MeasureTheory.IntegrableOn.mono_set hInt_ac ?_
    intro x hx
    exact ⟨le_trans hb hx.1, hx.2⟩
  have hInt_ab :
      IntervalIntegrable f MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hb).2 (hIntf b)
  have hInt_bc' :
      IntervalIntegrable f MeasureTheory.volume b c :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hbc).2 hInt_bc
  have hEq := intervalIntegral.integral_add_adjacent_intervals hInt_ab hInt_bc'
  linarith

/- Helper: domination by `g` bounds absolute interval integrals. -/
lemma abs_integral_le_of_bound {a : ℝ} {f g : ℝ → ℝ}
    (hIntg : ∀ c, MeasureTheory.IntegrableOn g (Set.Icc a c))
    (hbound : ∀ x, a ≤ x → |f x| ≤ g x) :
    ∀ {c}, a ≤ c → |∫ x in a..c, f x| ≤ ∫ x in a..c, g x := by
  intro c hc
  have hIntg' :
      IntervalIntegrable g MeasureTheory.volume a c :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hc).2 (hIntg c)
  have hbound_ae :
      ∀ᵐ t ∂(MeasureTheory.volume), t ∈ Set.Ioc a c → ‖f t‖ ≤ g t := by
    refine Filter.Eventually.of_forall ?_
    intro t ht
    have ht' : a ≤ t := le_of_lt ht.1
    simpa [Real.norm_eq_abs] using (hbound t ht')
  have hle :
      ‖∫ x in a..c, f x‖ ≤ ∫ x in a..c, g x := by
    simpa using
      (intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) (a := a) (b := c)
        (f := f) (g := g) hc hbound_ae hIntg')
  simpa [Real.norm_eq_abs] using hle

/- Helper: difference of partial integrals is controlled by `g`. -/
lemma abs_integral_diff_le {a : ℝ} {f g : ℝ → ℝ}
    (hIntf : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (hIntg : ∀ c, MeasureTheory.IntegrableOn g (Set.Icc a c))
    (hbound : ∀ x, a ≤ x → |f x| ≤ g x) :
    ∀ {b c}, a ≤ b → b ≤ c →
      |(∫ x in a..c, f x) - (∫ x in a..b, f x)| ≤ ∫ x in b..c, g x := by
  intro b c hb hbc
  have hEq :
      (∫ x in a..c, f x) - (∫ x in a..b, f x) = ∫ x in b..c, f x :=
    integral_diff_eq_interval (hIntf := hIntf) hb hbc
  have hbound_b : ∀ x, b ≤ x → |f x| ≤ g x := by
    intro x hx
    exact hbound x (le_trans hb hx)
  have hIntg_b : ∀ d, MeasureTheory.IntegrableOn g (Set.Icc b d) := by
    intro d
    have hInt_ad : MeasureTheory.IntegrableOn g (Set.Icc a d) := hIntg d
    exact MeasureTheory.IntegrableOn.mono_set hInt_ad (by
      intro x hx
      exact ⟨le_trans hb hx.1, hx.2⟩)
  have hle := abs_integral_le_of_bound (a := b) (f := f) (g := g) hIntg_b hbound_b (c := c) hbc
  simpa [hEq] using hle

/- Helper: dominated partial integrals form a Cauchy filter. -/
lemma cauchy_partial_integrals_of_comparison {a : ℝ} {f g : ℝ → ℝ} {lg : ℝ}
    (hIntf : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (hIntg : ∀ c, MeasureTheory.IntegrableOn g (Set.Icc a c))
    (hbound : ∀ x, a ≤ x → |f x| ≤ g x)
    (hconv : ImproperIntegralAtTop g a lg) :
    Cauchy (Filter.map (fun c : ℝ => ∫ x in a..c, f x) atTop) := by
  let F : ℝ → ℝ := fun c => ∫ x in a..c, f x
  let G : ℝ → ℝ := fun c => ∫ x in a..c, g x
  have hG : Tendsto G atTop (nhds lg) := hconv.2
  have hGdiff :
      Tendsto (fun p : ℝ × ℝ => G p.1 - G p.2) (atTop ×ˢ atTop) (nhds (lg - lg)) :=
    (hG.comp tendsto_fst).sub (hG.comp tendsto_snd)
  have hGabs :
      Tendsto (fun p : ℝ × ℝ => |G p.1 - G p.2|) (atTop ×ˢ atTop) (nhds 0) := by
    simpa using hGdiff.abs
  have hFle :
      (fun p : ℝ × ℝ => |F p.1 - F p.2|) ≤ᶠ[atTop ×ˢ atTop]
        fun p => |G p.1 - G p.2| := by
    have hmem : (Set.Ioi a : Set ℝ) ∈ (atTop : Filter ℝ) := Ioi_mem_atTop a
    have hmem_prod :
        (Set.Ioi a ×ˢ Set.Ioi a : Set (ℝ × ℝ)) ∈
          (atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ) :=
      Filter.prod_mem_prod hmem hmem
    have hEv : ∀ᶠ p in atTop ×ˢ atTop, a ≤ p.1 ∧ a ≤ p.2 := by
      refine eventually_of_mem hmem_prod ?_
      intro p hp
      exact ⟨le_of_lt hp.1, le_of_lt hp.2⟩
    refine hEv.mono ?_
    intro p hp
    have hp1 : a ≤ p.1 := hp.1
    have hp2 : a ≤ p.2 := hp.2
    have hposg : ∀ x, a ≤ x → 0 ≤ g x :=
      comparison_nonneg_g (f := f) (g := g) hbound
    cases le_total p.1 p.2 with
    | inl h12 =>
        have hdiff :
            |F p.2 - F p.1| ≤ ∫ x in p.1..p.2, g x := by
          simpa [F] using
            (abs_integral_diff_le (hIntf := hIntf) (hIntg := hIntg) (hbound := hbound)
              (b := p.1) (c := p.2) hp1 h12)
        have hEq :
            G p.2 - G p.1 = ∫ x in p.1..p.2, g x := by
          simpa [G] using
            (integral_diff_eq_interval (hIntf := hIntg) (b := p.1) (c := p.2) (a := a) hp1 h12)
        have hnonneg : 0 ≤ ∫ x in p.1..p.2, g x := by
          refine intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) (a := p.1) (b := p.2)
            h12 ?_
          intro x hx
          exact hposg x (le_trans hp1 hx.1)
        have hEqAbs : |G p.1 - G p.2| = ∫ x in p.1..p.2, g x := by
          have : |G p.2 - G p.1| = ∫ x in p.1..p.2, g x := by
            simp [hEq, abs_of_nonneg hnonneg]
          simpa [abs_sub_comm] using this
        simpa [abs_sub_comm, hEqAbs.symm] using hdiff
    | inr h21 =>
        have hdiff :
            |F p.1 - F p.2| ≤ ∫ x in p.2..p.1, g x := by
          simpa [F, abs_sub_comm] using
            (abs_integral_diff_le (hIntf := hIntf) (hIntg := hIntg) (hbound := hbound)
              (b := p.2) (c := p.1) hp2 h21)
        have hEq :
            G p.1 - G p.2 = ∫ x in p.2..p.1, g x := by
          simpa [G] using
            (integral_diff_eq_interval (hIntf := hIntg) (b := p.2) (c := p.1) (a := a) hp2 h21)
        have hnonneg : 0 ≤ ∫ x in p.2..p.1, g x := by
          refine intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) (a := p.2) (b := p.1)
            h21 ?_
          intro x hx
          exact hposg x (le_trans hp2 hx.1)
        have hEqAbs : |G p.1 - G p.2| = ∫ x in p.2..p.1, g x := by
          simp [hEq, abs_of_nonneg hnonneg]
        exact hdiff.trans_eq hEqAbs.symm
  have hLower :
      (fun p : ℝ × ℝ => -|G p.1 - G p.2|) ≤ᶠ[atTop ×ˢ atTop]
        fun p => F p.1 - F p.2 := by
    refine hFle.mono ?_
    intro p hp
    exact (abs_le.mp hp).1
  have hUpper :
      (fun p : ℝ × ℝ => F p.1 - F p.2) ≤ᶠ[atTop ×ˢ atTop]
        fun p => |G p.1 - G p.2| := by
    refine hFle.mono ?_
    intro p hp
    exact (abs_le.mp hp).2
  have hDiff :
      Tendsto (fun p : ℝ × ℝ => F p.1 - F p.2) (atTop ×ˢ atTop) (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hGabs.neg) hGabs hLower hUpper
  refine (IsUniformAddGroup.cauchy_map_iff_tendsto (𝓕 := atTop) (f := F)).2 ?_
  exact ⟨by infer_instance, hDiff⟩

/- Helper: pass eventual absolute bounds to the limit. -/
lemma limit_abs_le {F G : ℝ → ℝ} {lf lg : ℝ}
    (hF : Tendsto F atTop (nhds lf))
    (hG : Tendsto G atTop (nhds lg))
    (hbound : ∀ᶠ x in atTop, |F x| ≤ G x) :
    |lf| ≤ lg := by
  have hFabs : Tendsto (fun x => |F x|) atTop (nhds |lf|) := hF.abs
  exact tendsto_le_of_eventuallyLE hFabs hG hbound

/-- Proposition 5.5.5 (comparison test for improper integrals). Let
`f g : [a, ∞) → ℝ` be Riemann integrable on every `[a, b]` with `b > a` and
assume `|f x| ≤ g x` for all `x ≥ a`.
(i) If `∫ a^∞ g` converges, then `∫ a^∞ f` converges and
`|∫ a^∞ f| ≤ ∫ a^∞ g`.
(ii) If `∫ a^∞ f` diverges, then `∫ a^∞ g` diverges. -/
theorem improperIntegral_comparison {a : ℝ} {f g : ℝ → ℝ}
    (hIntf : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc a c))
    (hIntg : ∀ c, MeasureTheory.IntegrableOn g (Set.Icc a c))
    (hbound : ∀ x, a ≤ x → |f x| ≤ g x) :
    (∀ {lg : ℝ}, ImproperIntegralAtTop g a lg →
      ∃ lf : ℝ, ImproperIntegralAtTop f a lf ∧ |lf| ≤ lg) ∧
      (¬ ImproperIntegralAtTopConverges f a → ¬ ImproperIntegralAtTopConverges g a) :=
by
  have h1 :
      ∀ {lg : ℝ}, ImproperIntegralAtTop g a lg →
        ∃ lf : ℝ, ImproperIntegralAtTop f a lf ∧ |lf| ≤ lg := by
    intro lg hconv
    let F : ℝ → ℝ := fun c => ∫ x in a..c, f x
    let G : ℝ → ℝ := fun c => ∫ x in a..c, g x
    have hCauchy :
        Cauchy (Filter.map (fun c : ℝ => ∫ x in a..c, f x) atTop) :=
      cauchy_partial_integrals_of_comparison (hIntf := hIntf) (hIntg := hIntg)
        (hbound := hbound) hconv
    have hExists : ∃ lf, Tendsto F atTop (nhds lf) :=
      (cauchy_map_iff_exists_tendsto (l := atTop) (f := F)).1 hCauchy
    rcases hExists with ⟨lf, hF⟩
    have hF' : Tendsto (fun c : ℝ => ∫ x in a..c, f x) atTop (nhds lf) := by
      simpa [F] using hF
    have hFle : ∀ᶠ x in atTop, |F x| ≤ G x := by
      refine (eventually_of_mem (Ioi_mem_atTop a) ?_)
      intro x hx
      have hx' : a ≤ x := le_of_lt hx
      simpa [F, G] using
        (abs_integral_le_of_bound (a := a) (f := f) (g := g) hIntg hbound (c := x) hx')
    have hAbs : |lf| ≤ lg :=
      limit_abs_le (F := F) (G := G) (lf := lf) (lg := lg) hF hconv.2 hFle
    refine ⟨lf, ?_, hAbs⟩
    exact ⟨hIntf, hF'⟩
  refine ⟨h1, ?_⟩
  intro hdiv hconv
  rcases hconv with ⟨lg, hlg⟩
  rcases (h1 hlg) with ⟨lf, hlf, _⟩
  exact hdiv ⟨lf, hlf⟩

/- Helper: local integrability of the oscillatory integrand on `[a, c]` with `0 ≤ a`. -/
lemma integrableOn_sin_sq_over_cubic_Icc {a c : ℝ} (ha : 0 ≤ a) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => (Real.sin (x ^ 2) * (x + 2)) / (x ^ 3 + 1))
      (Set.Icc a c) := by
  have hcont :
      ContinuousOn (fun x : ℝ => (Real.sin (x ^ 2) * (x + 2)) / (x ^ 3 + 1)) (Set.Icc a c) := by
    refine (ContinuousOn.div ?hnum ?hden ?hneq)
    · have hnum' : Continuous (fun x : ℝ => Real.sin (x ^ 2) * (x + 2)) := by
        continuity
      exact hnum'.continuousOn
    · have hden' : Continuous (fun x : ℝ => x ^ 3 + 1) := by
        continuity
      exact hden'.continuousOn
    · intro x hx
      have hx0 : 0 ≤ x := le_trans ha hx.1
      have hx3 : 0 ≤ x ^ 3 := by exact pow_nonneg hx0 3
      have hpos : 0 < x ^ 3 + 1 := by linarith
      exact ne_of_gt hpos
  exact hcont.integrableOn_Icc

/- Helper: tail bound for the oscillatory integrand on `[1, ∞)`. -/
lemma bound_sin_sq_over_cubic {x : ℝ} (hx : 1 ≤ x) :
    |(Real.sin (x ^ 2) * (x + 2)) / (x ^ 3 + 1)| ≤ 3 / x ^ 2 := by
  have hx0 : 0 ≤ x := le_trans (show (0 : ℝ) ≤ 1 by linarith) hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hx3pos : 0 < x ^ 3 := by exact pow_pos hxpos 3
  have hx3nonneg : 0 ≤ x ^ 3 := le_of_lt hx3pos
  have hdenpos : 0 < x ^ 3 + 1 := by linarith
  have hnum_nonneg : 0 ≤ x + 2 := by linarith
  have hnum_le : x + 2 ≤ 3 * x := by nlinarith
  calc
    |(Real.sin (x ^ 2) * (x + 2)) / (x ^ 3 + 1)|
        = |Real.sin (x ^ 2) * (x + 2)| / (x ^ 3 + 1) := by
            simp [abs_div, abs_of_pos hdenpos]
    _ = |Real.sin (x ^ 2)| * |x + 2| / (x ^ 3 + 1) := by
            simp [abs_mul]
    _ ≤ 1 * |x + 2| / (x ^ 3 + 1) := by
            gcongr
            exact Real.abs_sin_le_one (x ^ 2)
    _ = |x + 2| / (x ^ 3 + 1) := by simp
    _ = (x + 2) / (x ^ 3 + 1) := by
            simp [abs_of_nonneg hnum_nonneg]
    _ ≤ (x + 2) / (x ^ 3) := by
            exact div_le_div_of_nonneg_left hnum_nonneg hx3pos (by linarith)
    _ ≤ (3 * x) / (x ^ 3) := by
            exact div_le_div_of_nonneg_right hnum_le hx3nonneg
    _ = 3 / x ^ 2 := by
            have hx0' : x ≠ 0 := by linarith
            calc
              (3 * x) / (x ^ 3) = (x * 3) / (x * x ^ 2) := by
                simp [pow_succ, mul_comm]
              _ = 3 / x ^ 2 := by
                simpa using (mul_div_mul_left (a := 3) (b := x ^ 2) (c := x) hx0')

/- Helper: the improper integral of `3 / x^2` from `1` equals `3`. -/
lemma improperIntegralAtTop_three_over_x_sq :
    ImproperIntegralAtTop (fun x : ℝ => 3 / x ^ 2) 1 3 := by
  have hbase : ImproperIntegralAtTop (fun x : ℝ => 1 / x ^ 2) 1 (1 : ℝ) := by
    have h : (2 : ℝ) - 1 = 1 := by norm_num
    simpa [h] using (improperIntegral_p_test 2).1 (by linarith)
  refine ⟨?hInt, ?hTend⟩
  · intro c
    have hInt0 :
        MeasureTheory.IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Set.Icc (1 : ℝ) c) :=
      hbase.1 c
    have hInt1 :
        MeasureTheory.IntegrableOn (fun x : ℝ => (1 / x ^ 2) * (3 : ℝ)) (Set.Icc (1 : ℝ) c) := by
      refine hInt0.mul_continuousOn (g' := fun _ : ℝ => (3 : ℝ)) ?_ ?_
      · simpa using
          (continuousOn_const : ContinuousOn (fun _ : ℝ => (3 : ℝ)) (Set.Icc (1 : ℝ) c))
      · simpa using (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) c))
    simpa [mul_comm, div_eq_mul_inv] using hInt1
  · have hTend :
        Tendsto (fun c : ℝ => 3 * ∫ x in 1..c, 1 / x ^ 2) atTop (nhds (3 * 1)) :=
      (Filter.Tendsto.const_mul 3 hbase.2)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hTend

/-- Example 5.5.6. The improper integral
`∫₀^∞ (sin (x^2) * (x + 2)) / (x^3 + 1)` converges, for instance by comparing
its tail to `3 / x^2` on `[1, ∞)` and using the tail test. -/
theorem improperIntegral_sin_sq_over_cubic_converges :
    ImproperIntegralAtTopConverges
      (fun x : ℝ => (Real.sin (x ^ 2) * (x + 2)) / (x ^ 3 + 1)) 0 :=
by
  let f : ℝ → ℝ := fun x => (Real.sin (x ^ 2) * (x + 2)) / (x ^ 3 + 1)
  let g : ℝ → ℝ := fun x => 3 / x ^ 2
  have hInt0 : ∀ c > 0, MeasureTheory.IntegrableOn f (Set.Icc 0 c) := by
    intro c _
    simpa [f] using (integrableOn_sin_sq_over_cubic_Icc (a := 0) (c := c) (ha := le_rfl))
  have hInt1 : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc 1 c) := by
    intro c
    simpa [f] using
      (integrableOn_sin_sq_over_cubic_Icc (a := 1) (c := c) (ha := (by exact zero_le_one)))
  have hconv_g : ImproperIntegralAtTop g 1 3 := by
    simpa [g] using improperIntegralAtTop_three_over_x_sq
  have hbound : ∀ x, 1 ≤ x → |f x| ≤ g x := by
    intro x hx
    simpa [f, g] using (bound_sin_sq_over_cubic (x := x) hx)
  have hconv_f_tail : ImproperIntegralAtTopConverges f 1 := by
    have hcomp :
        ∀ {lg : ℝ}, ImproperIntegralAtTop g 1 lg →
          ∃ lf : ℝ, ImproperIntegralAtTop f 1 lf ∧ |lf| ≤ lg :=
      (improperIntegral_comparison (a := 1) (f := f) (g := g)
        (hIntf := hInt1) (hIntg := hconv_g.1) (hbound := hbound)).1
    rcases hcomp hconv_g with ⟨lf, hlf, _⟩
    exact ⟨lf, hlf⟩
  have htail : ImproperIntegralAtTopConverges f 0 :=
    (improperIntegral_tail_convergence (f := f) (a := 0) (b := 1)
      (hb := by linarith) (hInt := hInt0)).1 hconv_f_tail
  simpa [f] using htail

/- Helper: shifting by a constant preserves divergence to `+∞`. -/
lemma tendsto_add_const_atTop (k : ℝ) :
    Tendsto (fun x : ℝ => x + k) atTop atTop := by
  refine tendsto_atTop_atTop.mpr ?_
  intro b
  refine ⟨b - k, ?_⟩
  intro x hx
  linarith

/- Helper: integrate `1 / (x - 1)` on `(2, c)` via a shift. -/
lemma intervalIntegral_one_div_sub {c : ℝ} (hc : 2 < c) :
    ∫ x in 2..c, 1 / (x - 1) = Real.log (c - 1) := by
  have hc' : 0 < c - 1 := by linarith
  have hcomp :
      ∫ x in 2..c, 1 / (x - 1) = ∫ x in (2 : ℝ) + (-1)..c + (-1), 1 / x := by
    simp [sub_eq_add_neg]
  have hcomp' :
      ∫ x in 2..c, 1 / (x - 1) = ∫ x in (1 : ℝ)..(c - 1), 1 / x := by
    have h2 : (2 : ℝ) + (-1) = 1 := by ring
    have h3 : c + (-1) = c - 1 := by ring
    simpa [h2, h3] using hcomp
  calc
    ∫ x in 2..c, 1 / (x - 1) = ∫ x in (1 : ℝ)..(c - 1), 1 / x := hcomp'
    _ = Real.log (c - 1) := by
      simpa using
        (integral_one_div_of_pos (a := (1 : ℝ)) (b := c - 1) zero_lt_one hc')

/- Helper: integrate `1 / (x + 1)` on `(2, c)` via a shift. -/
lemma intervalIntegral_one_div_add {c : ℝ} (hc : 2 < c) :
    ∫ x in 2..c, 1 / (x + 1) = Real.log (c + 1) - Real.log 3 := by
  have hc' : 0 < c + 1 := by linarith
  have hcomp :
      ∫ x in 2..c, 1 / (x + 1) = ∫ x in (2 : ℝ) + 1..c + 1, 1 / x := by
    simp
  have hcomp' :
      ∫ x in 2..c, 1 / (x + 1) = ∫ x in (3 : ℝ)..(c + 1), 1 / x := by
    have h2 : (2 : ℝ) + 1 = 3 := by ring
    simp [h2]
  calc
    ∫ x in 2..c, 1 / (x + 1) = ∫ x in (3 : ℝ)..(c + 1), 1 / x := hcomp'
    _ = Real.log ((c + 1) / 3) := by
      have hpos3 : 0 < (3 : ℝ) := by linarith
      simpa using (integral_one_div_of_pos (a := (3 : ℝ)) (b := c + 1) hpos3 hc')
    _ = Real.log (c + 1) - Real.log 3 := by
      have hne1 : (c + 1) ≠ 0 := by linarith
      have hne3 : (3 : ℝ) ≠ 0 := by norm_num
      simpa using (Real.log_div hne1 hne3)

/- Helper: interval integrability of `1 / (x - 1)` on `[2, c]` for `c > 2`. -/
lemma intervalIntegrable_one_div_sub {c : ℝ} (hc : 2 < c) :
    IntervalIntegrable (fun x : ℝ => 1 / (x - 1)) MeasureTheory.volume 2 c := by
  have hle : (2 : ℝ) ≤ c := by linarith
  have hcont_den : ContinuousOn (fun x : ℝ => x - 1) (Set.Icc 2 c) := by
    simpa [sub_eq_add_neg] using (continuousOn_id.sub continuousOn_const)
  have hden : ∀ x ∈ Set.Icc 2 c, x - 1 ≠ 0 := by
    intro x hx
    have hxpos : 0 < x - 1 := by linarith [hx.1]
    exact ne_of_gt hxpos
  have hcont : ContinuousOn (fun x : ℝ => 1 / (x - 1)) (Set.Icc 2 c) :=
    (continuousOn_const.div hcont_den hden)
  have hIntOn :
      MeasureTheory.IntegrableOn (fun x : ℝ => 1 / (x - 1)) (Set.Icc 2 c) :=
    hcont.integrableOn_Icc
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hle).2 hIntOn

/- Helper: interval integrability of `1 / (x + 1)` on `[2, c]` for `c > 2`. -/
lemma intervalIntegrable_one_div_add {c : ℝ} (hc : 2 < c) :
    IntervalIntegrable (fun x : ℝ => 1 / (x + 1)) MeasureTheory.volume 2 c := by
  have hle : (2 : ℝ) ≤ c := by linarith
  have hcont_den : ContinuousOn (fun x : ℝ => x + 1) (Set.Icc 2 c) := by
    simpa using (continuousOn_id.add continuousOn_const)
  have hden : ∀ x ∈ Set.Icc 2 c, x + 1 ≠ 0 := by
    intro x hx
    have hxpos : 0 < x + 1 := by linarith [hx.1]
    exact ne_of_gt hxpos
  have hcont : ContinuousOn (fun x : ℝ => 1 / (x + 1)) (Set.Icc 2 c) :=
    (continuousOn_const.div hcont_den hden)
  have hIntOn :
      MeasureTheory.IntegrableOn (fun x : ℝ => 1 / (x + 1)) (Set.Icc 2 c) :=
    hcont.integrableOn_Icc
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hle).2 hIntOn

/- Helper: evaluate the partial fractions integral on `(2, c)`. -/
lemma intervalIntegral_two_over_x_sq_sub_one {c : ℝ} (hc : 2 < c) :
    ∫ x in 2..c, 2 / (x ^ 2 - 1) =
      Real.log (c - 1) - Real.log (c + 1) + Real.log 3 := by
  have hEq :
      EqOn (fun x : ℝ => 2 / (x ^ 2 - 1))
        (fun x : ℝ => 1 / (x - 1) - 1 / (x + 1)) (Set.uIcc 2 c) := by
    intro x hx
    have hx' : x ∈ Set.Icc 2 c := by
      have hIcc : Set.uIcc 2 c = Set.Icc 2 c := Set.uIcc_of_le (by linarith)
      simpa [hIcc] using hx
    have hxne1 : x - 1 ≠ 0 := by
      have hxpos : 0 < x - 1 := by linarith [hx'.1]
      exact ne_of_gt hxpos
    have hxne2 : x + 1 ≠ 0 := by
      have hxpos : 0 < x + 1 := by linarith [hx'.1]
      exact ne_of_gt hxpos
    have hxden : x ^ 2 - 1 ≠ 0 := by
      have hxpos : 0 < x ^ 2 - 1 := by nlinarith [hx'.1]
      exact ne_of_gt hxpos
    field_simp [hxden, hxne1, hxne2]
    ring
  have hEqInt :
      ∫ x in 2..c, 2 / (x ^ 2 - 1) =
        ∫ x in 2..c, (1 / (x - 1) - 1 / (x + 1)) := by
    simpa using (intervalIntegral.integral_congr (μ := MeasureTheory.volume) hEq)
  have hsplit :
      ∫ x in 2..c, (1 / (x - 1) - 1 / (x + 1)) =
        (∫ x in 2..c, 1 / (x - 1)) - ∫ x in 2..c, 1 / (x + 1) := by
    simpa using
      (intervalIntegral.integral_sub (μ := MeasureTheory.volume)
        (intervalIntegrable_one_div_sub (c := c) hc)
        (intervalIntegrable_one_div_add (c := c) hc))
  calc
    ∫ x in 2..c, 2 / (x ^ 2 - 1) =
        ∫ x in 2..c, (1 / (x - 1) - 1 / (x + 1)) := hEqInt
    _ = (∫ x in 2..c, 1 / (x - 1)) - ∫ x in 2..c, 1 / (x + 1) := hsplit
    _ = Real.log (c - 1) - ∫ x in 2..c, 1 / (x + 1) := by
      rw [intervalIntegral_one_div_sub (c := c) hc]
    _ = Real.log (c - 1) - (Real.log (c + 1) - Real.log 3) := by
      rw [intervalIntegral_one_div_add (c := c) hc]
    _ = Real.log (c - 1) - Real.log (c + 1) + Real.log 3 := by ring

/- Helper: `log (c - 1) - log (c + 1)` tends to `0` as `c → ∞`. -/
lemma tendsto_log_sub_log_zero :
    Tendsto (fun c : ℝ => Real.log (c - 1) - Real.log (c + 1)) atTop (nhds 0) := by
  have hshift : Tendsto (fun c : ℝ => c + 1) atTop atTop :=
    tendsto_add_const_atTop 1
  have h := (Real.tendsto_log_comp_add_sub_log (-2)).comp hshift
  refine h.congr' ?_
  refine (Filter.Eventually.of_forall ?_)
  intro c
  have h' : (c + 1) + (-2) = c - 1 := by ring
  simp [h', sub_eq_add_neg, add_comm]

/- Helper: the shifted reciprocal integrals diverge at `∞`. -/
lemma divergence_shifted_one_div :
    ¬ ImproperIntegralAtTopConverges (fun x : ℝ => 1 / (x - 1)) 2 ∧
      ¬ ImproperIntegralAtTopConverges (fun x : ℝ => 1 / (x + 1)) 2 := by
  refine ⟨?hsub, ?hadd⟩
  · intro hconv
    rcases hconv with ⟨l, hl⟩
    have hEq :
        (fun c : ℝ => ∫ x in 2..c, 1 / (x - 1)) =ᶠ[atTop]
          fun c => Real.log (c - 1) := by
      refine (eventuallyEq_of_mem (Ioi_mem_atTop 2) ?_)
      intro c hc
      simpa using (intervalIntegral_one_div_sub (c := c) hc)
    have hshift : Tendsto (fun c : ℝ => c - 1) atTop atTop := by
      simpa [sub_eq_add_neg] using (tendsto_add_const_atTop (-1))
    have hlog : Tendsto (fun c : ℝ => Real.log (c - 1)) atTop atTop :=
      Real.tendsto_log_atTop.comp hshift
    have hTend :
        Tendsto (fun c : ℝ => ∫ x in 2..c, 1 / (x - 1)) atTop atTop :=
      hlog.congr' hEq.symm
    exact not_tendsto_nhds_of_tendsto_atTop hTend l (by simpa using hl.2)
  · intro hconv
    rcases hconv with ⟨l, hl⟩
    have hEq :
        (fun c : ℝ => ∫ x in 2..c, 1 / (x + 1)) =ᶠ[atTop]
          fun c => Real.log (c + 1) - Real.log 3 := by
      refine (eventuallyEq_of_mem (Ioi_mem_atTop 2) ?_)
      intro c hc
      simpa using (intervalIntegral_one_div_add (c := c) hc)
    have hshift : Tendsto (fun c : ℝ => c + 1) atTop atTop :=
      tendsto_add_const_atTop 1
    have hlog : Tendsto (fun c : ℝ => Real.log (c + 1)) atTop atTop :=
      Real.tendsto_log_atTop.comp hshift
    have hlog' : Tendsto (fun c : ℝ => Real.log (c + 1) - Real.log 3) atTop atTop := by
      simpa [sub_eq_add_neg] using
        (tendsto_atTop_add_const_right atTop (-Real.log (3 : ℝ)) hlog)
    have hTend :
        Tendsto (fun c : ℝ => ∫ x in 2..c, 1 / (x + 1)) atTop atTop :=
      hlog'.congr' hEq.symm
    exact not_tendsto_nhds_of_tendsto_atTop hTend l (by simpa using hl.2)

/- Helper: integrability of `2 / (x^2 - 1)` on `[2, c]`. -/
lemma integrableOn_two_over_x_sq_sub_one_Icc (c : ℝ) :
    MeasureTheory.IntegrableOn (fun x : ℝ => 2 / (x ^ 2 - 1)) (Set.Icc 2 c) := by
  by_cases hc : (2 : ℝ) ≤ c
  · have hcont_den : ContinuousOn (fun x : ℝ => x ^ 2 - 1) (Set.Icc 2 c) := by
      have hcont_sq : ContinuousOn (fun x : ℝ => x ^ 2) (Set.Icc 2 c) := by
        simpa [pow_two] using (continuousOn_id.mul continuousOn_id)
      simpa using hcont_sq.sub continuousOn_const
    have hden : ∀ x ∈ Set.Icc 2 c, x ^ 2 - 1 ≠ 0 := by
      intro x hx
      have hxpos : 0 < x ^ 2 - 1 := by nlinarith [hx.1]
      exact ne_of_gt hxpos
    have hcont : ContinuousOn (fun x : ℝ => 2 / (x ^ 2 - 1)) (Set.Icc 2 c) :=
      (continuousOn_const.div hcont_den hden)
    exact hcont.integrableOn_Icc
  · have hcc : Set.Icc (2 : ℝ) c = ∅ := Set.Icc_eq_empty_of_lt (lt_of_not_ge hc)
    simp [hcc]

/-- Example 5.5.7. The improper integral `∫₂^∞ 2 / (x^2 - 1)` converges (in
fact to `log 3`), but writing `2 / (x^2 - 1) = 1 / (x - 1) - 1 / (x + 1)` does
not allow splitting the improper integral, since both pieces diverge
separately. -/
theorem improperIntegral_partial_fraction_counterexample :
    ImproperIntegralAtTop (fun x : ℝ => 2 / (x ^ 2 - 1)) 2 (Real.log (3 : ℝ)) ∧
      ¬ ImproperIntegralAtTopConverges (fun x : ℝ => 1 / (x - 1)) 2 ∧
      ¬ ImproperIntegralAtTopConverges (fun x : ℝ => 1 / (x + 1)) 2 :=
by
  refine ⟨?hconv, divergence_shifted_one_div⟩
  refine ⟨?hInt, ?hTend⟩
  · intro c
    exact integrableOn_two_over_x_sq_sub_one_Icc c
  · have hEq :
        (fun c : ℝ => ∫ x in 2..c, 2 / (x ^ 2 - 1)) =ᶠ[atTop]
          fun c => Real.log (c - 1) - Real.log (c + 1) + Real.log (3 : ℝ) := by
      refine (eventuallyEq_of_mem (Ioi_mem_atTop 2) ?_)
      intro c hc
      simpa using (intervalIntegral_two_over_x_sq_sub_one (c := c) hc)
    have hTend0 :
        Tendsto (fun c : ℝ => Real.log (c - 1) - Real.log (c + 1) + Real.log (3 : ℝ)) atTop
          (nhds (Real.log (3 : ℝ))) := by
      have hlog : Tendsto (fun c : ℝ => Real.log (c - 1) - Real.log (c + 1)) atTop (nhds 0) :=
        tendsto_log_sub_log_zero
      have hconst :
          Tendsto (fun _ : ℝ => Real.log (3 : ℝ)) atTop (nhds (Real.log (3 : ℝ))) :=
        tendsto_const_nhds
      have hsum := hlog.add hconst
      simpa using hsum
    exact hTend0.congr' hEq.symm


/-- Definition 5.5.8. For a function `f : (a, b) → ℝ` that is Riemann
integrable on every closed subinterval `[c, d]` with `a < c < d < b`, the
improper integral `∫ a^b f` is defined as the iterated limit
`lim_{c → a⁺} lim_{d → b⁻} ∫_{c}^{d} f` when this limit exists. -/
def ImproperIntegralOpenInterval (f : ℝ → ℝ) (a b l : ℝ) : Prop :=
  (∀ ⦃c d⦄, a < c → c < d → d < b → MeasureTheory.IntegrableOn f (Set.Icc c d)) ∧
    Tendsto (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      (nhdsWithin a (Set.Ioi a) ×ˢ nhdsWithin b (Set.Iio b)) (nhds l)

/-- Definition 5.5.8 (whole line). If `f : ℝ → ℝ` is Riemann integrable on
every bounded interval `[a, b]`, then the improper integral `∫_{-∞}^{∞} f` is
defined as `lim_{c → -∞} lim_{d → ∞} ∫_{c}^{d} f`, when this limit exists. -/
def ImproperIntegralRealLine (f : ℝ → ℝ) (l : ℝ) : Prop :=
  (∀ a b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc a b)) ∧
    Tendsto (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (Filter.atBot ×ˢ Filter.atTop) (nhds l)

/- Helper: integrability of `x ↦ 1 / (1 + x^2)` on any closed interval. -/
lemma integrableOn_inv_one_plus_sq_Icc (a b : ℝ) :
    MeasureTheory.IntegrableOn (fun x : ℝ => 1 / (1 + x ^ 2)) (Set.Icc a b) := by
  simpa [one_div] using (integrable_inv_one_add_sq.integrableOn (s := Set.Icc a b))

/- Helper: interval integral of `1 / (1 + x^2)` via `arctan`. -/
lemma intervalIntegral_inv_one_add_sq_eq_arctan (a b : ℝ) :
    (∫ x in a..b, 1 / (1 + x ^ 2)) = arctan b - arctan a := by
  simp [one_div]

/- Helper: `arctan` difference tends to `π` on `(-∞, ∞)`. -/
lemma tendsto_arctan_diff_atBot_atTop :
    Tendsto (fun p : ℝ × ℝ => arctan p.2 - arctan p.1) (Filter.atBot ×ˢ Filter.atTop)
      (nhds (π : ℝ)) := by
  have htop : Tendsto arctan atTop (nhds (π / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop
  have hbot : Tendsto arctan atBot (nhds (-(π / 2))) :=
    tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot
  have hsnd :
      Tendsto (fun p : ℝ × ℝ => arctan p.2) (Filter.atBot ×ˢ Filter.atTop) (nhds (π / 2)) :=
    htop.comp tendsto_snd
  have hfst :
      Tendsto (fun p : ℝ × ℝ => arctan p.1) (Filter.atBot ×ˢ Filter.atTop)
        (nhds (-(π / 2))) :=
    hbot.comp tendsto_fst
  have hsub := hsnd.sub hfst
  have hpi : (π / 2) - (-(π / 2)) = (π : ℝ) := by ring
  simpa [hpi] using hsub

/-- Example 5.5.9. The improper integral of `1 / (1 + x^2)` over the entire real
line converges and has value `π`, computed via the antiderivative `x ↦ arctan x`
and the limits at `±∞`. -/
theorem improperIntegral_real_line_inv_one_plus_sq :
    ImproperIntegralRealLine (fun x : ℝ => 1 / (1 + x ^ 2)) Real.pi :=
by
  refine ⟨?hInt, ?hTend⟩
  · intro a b
    exact integrableOn_inv_one_plus_sq_Icc a b
  · have hEq :
        (fun p : ℝ × ℝ => ∫ x in p.1..p.2, 1 / (1 + x ^ 2)) =ᶠ[Filter.atBot ×ˢ Filter.atTop]
          fun p => arctan p.2 - arctan p.1 := by
      refine Filter.Eventually.of_forall ?_
      intro p
      exact intervalIntegral_inv_one_add_sq_eq_arctan p.1 p.2
    have hTend :
        Tendsto (fun p : ℝ × ℝ => arctan p.2 - arctan p.1) (Filter.atBot ×ˢ Filter.atTop)
          (nhds (Real.pi)) := by
      simpa using tendsto_arctan_diff_atBot_atTop
    exact hTend.congr' hEq.symm

/-- Helper: integrability on all closed intervals implies interval integrability. -/
lemma intervalIntegrable_of_integrableOn_Icc {f : ℝ → ℝ}
    (hInt : ∀ a b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc a b)) (a b : ℝ) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  by_cases hab : a ≤ b
  · exact
      (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hab).2
        (hInt a b)
  · have hba : b ≤ a := le_of_not_ge hab
    have hba' :
        IntervalIntegrable f MeasureTheory.volume b a :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hba).2
        (hInt b a)
    exact hba'.symm

/-- Helper: express an interval integral via the basepoint `0`. -/
lemma intervalIntegral_eq_sub_base {f : ℝ → ℝ}
    (hInt : ∀ a b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc a b)) (a b : ℝ) :
    (∫ x in a..b, f x) = (∫ x in 0..b, f x) - (∫ x in 0..a, f x) := by
  have hInt0a : IntervalIntegrable f MeasureTheory.volume 0 a :=
    intervalIntegrable_of_integrableOn_Icc hInt 0 a
  have hIntab : IntervalIntegrable f MeasureTheory.volume a b :=
    intervalIntegrable_of_integrableOn_Icc hInt a b
  have hEq :
      (∫ x in 0..a, f x) + ∫ x in a..b, f x = ∫ x in 0..b, f x :=
    intervalIntegral.integral_add_adjacent_intervals hInt0a hIntab
  linarith

/-- Helper: convergence of base integrals at `-∞` gives left partial limits. -/
lemma tendsto_intervalIntegral_atBot_of_base {f : ℝ → ℝ}
    (hInt : ∀ a b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc a b)) {Lminus : ℝ}
    (hbot : Tendsto (fun t : ℝ => ∫ x in 0..t, f x) atBot (nhds Lminus)) (b : ℝ) :
    Tendsto (fun a : ℝ => ∫ x in a..b, f x) atBot (nhds ((∫ x in 0..b, f x) - Lminus)) := by
  have hEq :
      (fun a : ℝ => ∫ x in a..b, f x) =ᶠ[atBot]
        fun a => (∫ x in 0..b, f x) - (∫ x in 0..a, f x) := by
    refine Filter.Eventually.of_forall ?_
    intro a
    simpa using intervalIntegral_eq_sub_base (f := f) hInt a b
  have hconst :
      Tendsto (fun _ : ℝ => ∫ x in 0..b, f x) atBot (nhds (∫ x in 0..b, f x)) :=
    tendsto_const_nhds
  have hsub := hconst.sub hbot
  exact hsub.congr' hEq.symm

/-- Helper: base limits at `±∞` yield the two-variable limit. -/
lemma tendsto_intervalIntegral_atBot_atTop_of_base {f : ℝ → ℝ}
    (hInt : ∀ a b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc a b))
    {Lminus Lplus : ℝ}
    (hbot : Tendsto (fun t : ℝ => ∫ x in 0..t, f x) atBot (nhds Lminus))
    (htop : Tendsto (fun t : ℝ => ∫ x in 0..t, f x) atTop (nhds Lplus)) :
    Tendsto (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (Filter.atBot ×ˢ Filter.atTop)
      (nhds (Lplus - Lminus)) := by
  have hEq :
      (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) =ᶠ[Filter.atBot ×ˢ Filter.atTop]
        fun p => (∫ x in 0..p.2, f x) - (∫ x in 0..p.1, f x) := by
    refine Filter.Eventually.of_forall ?_
    intro p
    simpa using intervalIntegral_eq_sub_base (f := f) hInt p.1 p.2
  have hsnd :
      Tendsto (fun p : ℝ × ℝ => ∫ x in 0..p.2, f x) (Filter.atBot ×ˢ Filter.atTop)
        (nhds Lplus) :=
    htop.comp tendsto_snd
  have hfst :
      Tendsto (fun p : ℝ × ℝ => ∫ x in 0..p.1, f x) (Filter.atBot ×ˢ Filter.atTop)
        (nhds Lminus) :=
    hbot.comp tendsto_fst
  have hsub := hsnd.sub hfst
  exact hsub.congr' hEq.symm

/-- Proposition 5.5.10. If `f : ℝ → ℝ` is Riemann integrable on every bounded
interval `[a, b]`, then the iterated limits
`lim_{a → -∞} lim_{b → ∞} ∫_{a}^{b} f` and
`lim_{b → ∞} lim_{a → -∞} ∫_{a}^{b} f` converge together and have the same
value. If either iterated limit exists, then the improper integral over the
whole line converges to the same value and agrees with the limit of the
symmetric integrals `∫_{-a}^{a} f` as `a → ∞`. -/
theorem improperIntegral_iterated_limits_symm {f : ℝ → ℝ}
    (hInt : ∀ a b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc a b)) :
    ((∃ g l,
        (∀ a, Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds (g a))) ∧
        Tendsto g atBot (nhds l)) ↔
      (∃ h l,
        (∀ b, Tendsto (fun a : ℝ => ∫ x in a..b, f x) atBot (nhds (h b))) ∧
        Tendsto h atTop (nhds l)))
    ∧
      (∀ g h l₁ l₂,
        (∀ a, Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds (g a))) →
        Tendsto g atBot (nhds l₁) →
        (∀ b, Tendsto (fun a : ℝ => ∫ x in a..b, f x) atBot (nhds (h b))) →
        Tendsto h atTop (nhds l₂) →
        l₁ = l₂)
    ∧
      ((∃ g l,
        (∀ a, Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds (g a))) ∧
        Tendsto g atBot (nhds l)) →
        ∃ l,
          ImproperIntegralRealLine f l ∧
            Tendsto (fun a : ℝ => ∫ x in (-a)..a, f x) atTop (nhds l)) :=
by
  classical
  let F : ℝ → ℝ := fun t => ∫ x in 0..t, f x
  have hEqInt : ∀ a b, ∫ x in a..b, f x = F b - F a := by
    intro a b
    simpa [F] using intervalIntegral_eq_sub_base (f := f) hInt a b
  have hF0 : F 0 = 0 := by simp [F]
  refine ⟨?hEquiv, ?hUnique, ?hSymm⟩
  · constructor
    · intro hR
      rcases hR with ⟨g, l, hg, hglim⟩
      let Lplus : ℝ := g 0
      have hTop : Tendsto F atTop (nhds Lplus) := by
        simpa [F, Lplus] using hg 0
      have hg_eq : ∀ a, g a = Lplus - F a := by
        intro a
        have h1 : Tendsto (fun b => F b - F a) atTop (nhds (g a)) := by
          simpa [hEqInt] using hg a
        have h2 : Tendsto (fun b => F b - F a) atTop (nhds (Lplus - F a)) :=
          hTop.sub tendsto_const_nhds
        exact tendsto_nhds_unique h1 h2
      have hglim' : Tendsto (fun a => Lplus - F a) atBot (nhds l) := by
        have hEq : (fun a => g a) = fun a => Lplus - F a := by
          funext a
          exact hg_eq a
        simpa [hEq] using hglim
      let Lminus : ℝ := Lplus - l
      have hbot : Tendsto F atBot (nhds Lminus) := by
        have hconst : Tendsto (fun _ : ℝ => Lplus) atBot (nhds Lplus) := tendsto_const_nhds
        have h := (hconst.sub hglim')
        have hfun : (fun a => Lplus - (Lplus - F a)) = fun a => F a := by
          funext a
          ring
        simpa [Lminus, hfun] using h
      let h : ℝ → ℝ := fun b => F b - Lminus
      have hhlim : ∀ b, Tendsto (fun a : ℝ => ∫ x in a..b, f x) atBot (nhds (h b)) := by
        intro b
        have htemp :=
          tendsto_intervalIntegral_atBot_of_base (f := f) hInt (b := b) hbot
        simpa [h, F, Lminus] using htemp
      have hhtend : Tendsto h atTop (nhds l) := by
        have htemp : Tendsto (fun b => F b - Lminus) atTop (nhds (Lplus - Lminus)) :=
          hTop.sub tendsto_const_nhds
        have hval : Lplus - Lminus = l := by
          simp [Lminus]
        simpa [h, hval] using htemp
      exact ⟨h, l, hhlim, hhtend⟩
    · intro hL
      rcases hL with ⟨h, l, hh, hhtend⟩
      have hh0 : Tendsto (fun a : ℝ => ∫ x in a..(0 : ℝ), f x) atBot (nhds (h 0)) := hh 0
      have hh0' : Tendsto (fun a : ℝ => -F a) atBot (nhds (h 0)) := by
        simpa [hEqInt, hF0] using hh0
      let Lminus : ℝ := -h 0
      have hbot : Tendsto F atBot (nhds Lminus) := by
        have hconst :
            Tendsto (fun _ : ℝ => (0 : ℝ)) atBot (nhds (0 : ℝ)) := tendsto_const_nhds
        have h := (hconst.sub hh0')
        have hfun : (fun a => (0 : ℝ) - (-F a)) = fun a => F a := by
          funext a
          ring
        simpa [Lminus, hfun] using h
      have hh_eq : ∀ b, h b = F b - Lminus := by
        intro b
        have h1 : Tendsto (fun a : ℝ => ∫ x in a..b, f x) atBot (nhds (h b)) := hh b
        have h2 :
            Tendsto (fun a : ℝ => ∫ x in a..b, f x) atBot (nhds (F b - Lminus)) := by
          have h2' :=
            tendsto_intervalIntegral_atBot_of_base (f := f) hInt (b := b) hbot
          simpa [F] using h2'
        exact tendsto_nhds_unique h1 h2
      have hhtend' : Tendsto (fun b => F b - Lminus) atTop (nhds l) := by
        have hEq : (fun b => h b) = fun b => F b - Lminus := by
          funext b
          exact hh_eq b
        simpa [hEq] using hhtend
      let Lplus : ℝ := Lminus + l
      have hTop : Tendsto F atTop (nhds Lplus) := by
        have hconst : Tendsto (fun _ : ℝ => Lminus) atTop (nhds Lminus) := tendsto_const_nhds
        have htemp := (hconst.add hhtend')
        have hfun : (fun b => Lminus + (F b - Lminus)) = fun b => F b := by
          funext b
          ring
        simpa [Lplus, hfun] using htemp
      let g : ℝ → ℝ := fun a => Lplus - F a
      have hg : ∀ a, Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds (g a)) := by
        intro a
        have htemp : Tendsto (fun b => F b - F a) atTop (nhds (Lplus - F a)) :=
          hTop.sub tendsto_const_nhds
        simpa [g, hEqInt] using htemp
      have hglim : Tendsto g atBot (nhds l) := by
        have hconst : Tendsto (fun _ : ℝ => Lplus) atBot (nhds Lplus) := tendsto_const_nhds
        have htemp : Tendsto (fun a => Lplus - F a) atBot (nhds (Lplus - Lminus)) :=
          hconst.sub hbot
        have hval : Lplus - Lminus = l := by
          simp [Lplus]
        simpa [g, hval] using htemp
      exact ⟨g, l, hg, hglim⟩
  · intro g h l₁ l₂ hg hglim hh hhtend
    let Lplus : ℝ := g 0
    have hTop : Tendsto F atTop (nhds Lplus) := by
      simpa [F, Lplus] using hg 0
    have hg_eq : ∀ a, g a = Lplus - F a := by
      intro a
      have h1 : Tendsto (fun b => F b - F a) atTop (nhds (g a)) := by
        simpa [hEqInt] using hg a
      have h2 : Tendsto (fun b => F b - F a) atTop (nhds (Lplus - F a)) :=
        hTop.sub tendsto_const_nhds
      exact tendsto_nhds_unique h1 h2
    have hglim' : Tendsto (fun a => Lplus - F a) atBot (nhds l₁) := by
      have hEq : (fun a => g a) = fun a => Lplus - F a := by
        funext a
        exact hg_eq a
      simpa [hEq] using hglim
    let Lminus : ℝ := Lplus - l₁
    have hbot : Tendsto F atBot (nhds Lminus) := by
      have hconst : Tendsto (fun _ : ℝ => Lplus) atBot (nhds Lplus) := tendsto_const_nhds
      have h := (hconst.sub hglim')
      have hfun : (fun a => Lplus - (Lplus - F a)) = fun a => F a := by
        funext a
        ring
      simpa [Lminus, hfun] using h
    have hh_eq : ∀ b, h b = F b - Lminus := by
      intro b
      have h1 : Tendsto (fun a : ℝ => ∫ x in a..b, f x) atBot (nhds (h b)) := hh b
      have h2 :
          Tendsto (fun a : ℝ => ∫ x in a..b, f x) atBot (nhds (F b - Lminus)) := by
        have h2' :=
          tendsto_intervalIntegral_atBot_of_base (f := f) hInt (b := b) hbot
        simpa [F] using h2'
      exact tendsto_nhds_unique h1 h2
    have hhtend' : Tendsto (fun b => F b - Lminus) atTop (nhds l₂) := by
      have hEq : (fun b => h b) = fun b => F b - Lminus := by
        funext b
        exact hh_eq b
      simpa [hEq] using hhtend
    have hlimit : Tendsto (fun b => F b - Lminus) atTop (nhds (Lplus - Lminus)) :=
      hTop.sub tendsto_const_nhds
    have hl2 : l₂ = Lplus - Lminus := tendsto_nhds_unique hhtend' hlimit
    have hl1 : Lplus - Lminus = l₁ := by
      simp [Lminus]
    simpa [hl1] using hl2.symm
  · intro hR
    rcases hR with ⟨g, l, hg, hglim⟩
    let Lplus : ℝ := g 0
    have hTop : Tendsto F atTop (nhds Lplus) := by
      simpa [F, Lplus] using hg 0
    have hg_eq : ∀ a, g a = Lplus - F a := by
      intro a
      have h1 : Tendsto (fun b => F b - F a) atTop (nhds (g a)) := by
        simpa [hEqInt] using hg a
      have h2 : Tendsto (fun b => F b - F a) atTop (nhds (Lplus - F a)) :=
        hTop.sub tendsto_const_nhds
      exact tendsto_nhds_unique h1 h2
    have hglim' : Tendsto (fun a => Lplus - F a) atBot (nhds l) := by
      have hEq : (fun a => g a) = fun a => Lplus - F a := by
        funext a
        exact hg_eq a
      simpa [hEq] using hglim
    let Lminus : ℝ := Lplus - l
    have hbot : Tendsto F atBot (nhds Lminus) := by
      have hconst : Tendsto (fun _ : ℝ => Lplus) atBot (nhds Lplus) := tendsto_const_nhds
      have h := (hconst.sub hglim')
      have hfun : (fun a => Lplus - (Lplus - F a)) = fun a => F a := by
        funext a
        ring
      simpa [Lminus, hfun] using h
    have hProd :
        Tendsto (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (Filter.atBot ×ˢ Filter.atTop)
          (nhds (Lplus - Lminus)) :=
      tendsto_intervalIntegral_atBot_atTop_of_base (f := f) hInt hbot hTop
    have hval : Lplus - Lminus = l := by
      simp [Lminus]
    have hImp : ImproperIntegralRealLine f l := by
      refine ⟨hInt, ?_⟩
      simpa [hval] using hProd
    have hpair : Tendsto (fun a : ℝ => (-a, a)) atTop (Filter.atBot ×ˢ Filter.atTop) :=
      tendsto_neg_atTop_atBot.prodMk tendsto_id
    have hSymmTend :
        Tendsto (fun a : ℝ => ∫ x in (-a)..a, f x) atTop (nhds l) := by
      have hcomp := hProd.comp hpair
      simpa [hval] using hcomp
    exact ⟨l, hImp, hSymmTend⟩

/-- Example 5.5.11. For the function `f(x) = x / |x|` with `f(0) = 0`,
integrable on every bounded interval, the improper integral over the whole
line does not converge because for any fixed `a < 0` the limit
`lim_{b → ∞} ∫_{a}^{b} f` diverges. However, the symmetric partial integrals
`∫_{-a}^{a} f` are all zero for `a > 0`, so
`lim_{a → ∞} ∫_{-a}^{a} f = 0`. -/
theorem improperIntegral_sign_diverges_but_symmetric_zero :
    (∀ a : ℝ, a < 0 →
      ¬ ImproperIntegralAtTopConverges (fun x : ℝ => if x = 0 then 0 else x / |x|) a) ∧
      Tendsto (fun a : ℝ => ∫ x in (-a)..a, (if x = 0 then 0 else x / |x|)) atTop (nhds 0) :=
by
  classical
  let f : ℝ → ℝ := fun x => if x = 0 then 0 else x / |x|
  have hEq_neg :
      ∀ {a : ℝ}, a < 0 →
        f =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a 0)] fun _ => (-1 : ℝ) := by
    intro a ha
    have hmem :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.uIoc a 0)), x ∈ (Set.uIoc a 0) := by
      simpa using
        (MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) (s := (Set.uIoc a 0))
          (by simpa using (measurableSet_uIoc : MeasurableSet (Set.uIoc (a : ℝ) 0))))
    have hne :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.uIoc a 0)), x ≠ (0 : ℝ) := by
      simpa using
        (MeasureTheory.Measure.ae_ne (MeasureTheory.volume.restrict (Set.uIoc a 0)) (0 : ℝ))
    refine (hmem.and hne).mono ?_
    intro x hx
    have hxmem : x ∈ Set.Ioc a 0 := by
      have hle : (a : ℝ) ≤ 0 := le_of_lt ha
      simpa [Set.uIoc_of_le hle] using hx.1
    have hxle : x ≤ 0 := hxmem.2
    have hxlt : x < 0 := lt_of_le_of_ne hxle hx.2
    have hxne : x ≠ 0 := hx.2
    calc
      f x = x / |x| := by simp [f, hxne]
      _ = x / (-x) := by simp [abs_of_neg hxlt]
      _ = -(x / x) := by simp [div_neg]
      _ = (-1 : ℝ) := by simp [hxne]
  have hEq_pos :
      ∀ {b : ℝ}, 0 < b → EqOn f (fun _ => (1 : ℝ)) (Set.uIoc 0 b) := by
    intro b hb x hx
    have hxmem : x ∈ Set.Ioc (0 : ℝ) b := by
      simpa [Set.uIoc_of_le (le_of_lt hb)] using hx
    have hxpos : 0 < x := hxmem.1
    calc
      f x = x / |x| := by simp [f, hxpos.ne']
      _ = x / x := by simp [abs_of_pos hxpos]
      _ = (1 : ℝ) := by simp [hxpos.ne']
  have hInt_a0 : ∀ {a : ℝ}, a < 0 → (∫ x in a..0, f x) = a := by
    intro a ha
    have hEq := hEq_neg (a := a) ha
    have hInt :
        ∫ x in a..0, f x = ∫ x in a..0, (-1 : ℝ) := by
      simpa using
        (intervalIntegral.integral_congr_ae_restrict (a := a) (b := 0)
          (μ := MeasureTheory.volume) hEq)
    calc
      ∫ x in a..0, f x = ∫ x in a..0, (-1 : ℝ) := hInt
      _ = (0 - a) * (-1 : ℝ) := by simp
      _ = a := by ring
  have hInt_0b : ∀ {b : ℝ}, 0 < b → (∫ x in 0..b, f x) = b := by
    intro b hb
    have hEq := hEq_pos (b := b) hb
    have hInt :
        ∫ x in 0..b, f x = ∫ x in 0..b, (1 : ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      exact hEq hx
    calc
      ∫ x in 0..b, f x = ∫ x in 0..b, (1 : ℝ) := hInt
      _ = b := by simp
  have hInt_a0_int : ∀ {a : ℝ}, a < 0 → IntervalIntegrable f MeasureTheory.volume a 0 := by
    intro a ha
    have hEq := hEq_neg (a := a) ha
    have hconst :
        IntervalIntegrable (fun _ : ℝ => (-1 : ℝ)) MeasureTheory.volume a 0 :=
      intervalIntegrable_const
    exact (intervalIntegrable_congr_ae (f := f) (g := fun _ : ℝ => (-1 : ℝ)) hEq).2 hconst
  have hInt_0b_int : ∀ {b : ℝ}, 0 < b → IntervalIntegrable f MeasureTheory.volume 0 b := by
    intro b hb
    have hEq := hEq_pos (b := b) hb
    have hconst :
        IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 b :=
      intervalIntegrable_const
    exact (intervalIntegrable_congr (f := f) (g := fun _ : ℝ => (1 : ℝ)) hEq).2 hconst
  have hlim : ∀ {a : ℝ}, a < 0 →
      Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop atTop := by
    intro a ha
    have hEq :
        (fun b : ℝ => ∫ x in a..b, f x) =ᶠ[atTop] fun b => b + a := by
      refine (eventuallyEq_of_mem (Ioi_mem_atTop 0) ?_)
      intro b hb
      have hsplit :=
        intervalIntegral.integral_add_adjacent_intervals
          (hInt_a0_int (a := a) ha) (hInt_0b_int (b := b) hb)
      calc
        ∫ x in a..b, f x = (∫ x in a..0, f x) + ∫ x in 0..b, f x := hsplit.symm
        _ = a + b := by
          simp [hInt_a0 (a := a) ha, hInt_0b (b := b) hb]
        _ = b + a := by ac_rfl
    have hTend : Tendsto (fun b : ℝ => b + a) atTop atTop := tendsto_add_const_atTop a
    exact hTend.congr' hEq.symm
  refine ⟨?hdiv, ?hsymm⟩
  · intro a ha hconv
    rcases hconv with ⟨l, hl⟩
    have hTend := hlim (a := a) ha
    exact not_tendsto_nhds_of_tendsto_atTop hTend l (by simpa using hl.2)
  · have hEq :
        (fun a : ℝ => ∫ x in (-a)..a, f x) =ᶠ[atTop] fun _ => (0 : ℝ) := by
      refine (eventuallyEq_of_mem (Ioi_mem_atTop 0) ?_)
      intro a ha
      have ha' : 0 < a := by simpa using ha
      have hInt1 := hInt_a0 (a := -a) (by linarith [ha'])
      have hInt2 := hInt_0b (b := a) ha
      have hsplit :=
        intervalIntegral.integral_add_adjacent_intervals
          (hInt_a0_int (a := -a) (by linarith [ha'])) (hInt_0b_int (b := a) ha)
      calc
        ∫ x in (-a)..a, f x = (∫ x in (-a)..0, f x) + ∫ x in 0..a, f x := hsplit.symm
        _ = (-a) + a := by
          simp [hInt1, hInt2]
        _ = (0 : ℝ) := by ring
    have hTend : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds (0 : ℝ)) :=
      tendsto_const_nhds
    exact hTend.congr' hEq.symm

/-- Example 5.5.12. The sinc function is defined by
`sinc x = sin x / x` for `x ≠ 0` and `sinc 0 = 1`. Its improper integral over
the whole real line converges to `π`, while the improper integral of its
absolute value diverges. -/
noncomputable def sinc (x : ℝ) : ℝ := if x = 0 then 1 else Real.sin x / x

/-- Tail bound for the sinc primitive on positive intervals. -/
lemma sinc_tail_bound {s t : ℝ} (hs : (1 : ℝ) ≤ s) (hst : s ≤ t) :
    |∫ x in s..t, _root_.sinc x| ≤ 3 / s := by
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have ht_pos : 0 < t := lt_of_lt_of_le hs_pos hst
  have h_nozero : ∀ x ∈ Set.uIcc s t, x ≠ 0 := by
    intro x hx
    have hx' : x ∈ Set.Icc s t := by simpa [Set.uIcc_of_le hst] using hx
    exact ne_of_gt (lt_of_lt_of_le hs_pos hx'.1)
  have hu :
      ∀ x ∈ Set.uIcc s t, HasDerivAt (fun y : ℝ => y⁻¹) (-((x ^ 2)⁻¹)) x := by
    intro x hx
    simpa [pow_two, sq] using (hasDerivAt_inv (h_nozero x hx))
  have hv :
      ∀ x ∈ Set.uIcc s t, HasDerivAt (fun y : ℝ => -Real.cos y) (Real.sin x) x := by
    intro x hx
    simpa using (hasDerivAt_cos x).neg
  have huInt :
      IntervalIntegrable (fun x : ℝ => -((x ^ 2)⁻¹)) MeasureTheory.volume s t := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ((continuousOn_id.pow 2).inv₀ ?_).neg
    intro x hx
    exact pow_ne_zero 2 (h_nozero x hx)
  have hvInt :
      IntervalIntegrable (fun x : ℝ => Real.sin x) MeasureTheory.volume s t := by
    exact Real.continuous_sin.intervalIntegrable s t
  have hparts :
      ∫ x in s..t, x⁻¹ * Real.sin x
        = t⁻¹ * (-Real.cos t) - s⁻¹ * (-Real.cos s)
          - ∫ x in s..t, -((x ^ 2)⁻¹) * (-Real.cos x) := by
    simpa using intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv huInt hvInt
  have hsinc_eq :
      ∫ x in s..t, _root_.sinc x = ∫ x in s..t, x⁻¹ * Real.sin x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hxne : x ≠ 0 := h_nozero x hx
    simp [_root_.sinc, hxne, div_eq_mul_inv, mul_comm]
  have h_inv_sq_int :
      ∫ x in s..t, (x ^ 2)⁻¹ = s⁻¹ - t⁻¹ := by
    have hz : (0 : ℝ) ∉ Set.uIcc s t := Set.notMem_uIcc_of_lt hs_pos ht_pos
    have h_rpow0 :
        ∫ x in s..t, x ^ (-2 : ℝ)
          = (t ^ ((-2 : ℝ) + 1) - s ^ ((-2 : ℝ) + 1)) / ((-2 : ℝ) + 1) := by
      have hcond : (-1 : ℝ) < (-2 : ℝ) ∨ ((-2 : ℝ) ≠ (-1 : ℝ) ∧ (0 : ℝ) ∉ Set.uIcc s t) := by
        right
        exact ⟨by norm_num, hz⟩
      simpa using (integral_rpow (a := s) (b := t) (r := (-2 : ℝ)) hcond)
    have h_rpow :
        ∫ x in s..t, (x ^ 2)⁻¹ = (t ^ (-1 : ℝ) - s ^ (-1 : ℝ)) / (-1 : ℝ) := by
      have hm : ((-2 : ℝ) + 1) = (-1 : ℝ) := by norm_num
      simpa [hm] using h_rpow0
    calc
      ∫ x in s..t, (x ^ 2)⁻¹ = (t ^ (-1 : ℝ) - s ^ (-1 : ℝ)) / (-1 : ℝ) := h_rpow
      _ = s⁻¹ - t⁻¹ := by
        ring_nf
        simp [Real.rpow_neg_one]
        ring
  have h_term1 :
      |t⁻¹ * (-Real.cos t)| ≤ t⁻¹ := by
    have ht_inv_nonneg : 0 ≤ t⁻¹ := inv_nonneg.mpr ht_pos.le
    calc
      |t⁻¹ * (-Real.cos t)| = |t⁻¹| * |Real.cos t| := by simp [abs_mul]
      _ ≤ |t⁻¹| * 1 := by gcongr; exact abs_cos_le_one t
      _ = t⁻¹ := by simp [abs_of_nonneg ht_inv_nonneg]
  have h_term2 :
      |s⁻¹ * (-Real.cos s)| ≤ s⁻¹ := by
    have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs_pos.le
    calc
      |s⁻¹ * (-Real.cos s)| = |s⁻¹| * |Real.cos s| := by simp [abs_mul]
      _ ≤ |s⁻¹| * 1 := by gcongr; exact abs_cos_le_one s
      _ = s⁻¹ := by simp [abs_of_nonneg hs_inv_nonneg]
  have h_rem_int :
      |∫ x in s..t, -((x ^ 2)⁻¹) * (-Real.cos x)| ≤ ∫ x in s..t, (x ^ 2)⁻¹ := by
    have h_int_abs :
        IntervalIntegrable (fun x : ℝ => |(-((x ^ 2)⁻¹) * (-Real.cos x))|) MeasureTheory.volume s t := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ((((continuousOn_id.pow 2).inv₀ ?_).neg.mul (Real.continuous_cos.continuousOn.neg)).abs)
      intro x hx
      exact pow_ne_zero 2 (h_nozero x hx)
    have h_int_rhs :
        IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) MeasureTheory.volume s t := by
      refine ContinuousOn.intervalIntegrable ?_
      refine (continuousOn_id.pow 2).inv₀ ?_
      intro x hx
      exact pow_ne_zero 2 (h_nozero x hx)
    have h_point :
        ∀ x ∈ Set.Icc s t, |(-((x ^ 2)⁻¹) * (-Real.cos x))| ≤ (x ^ 2)⁻¹ := by
      intro x hx
      have hx_inv_nonneg : 0 ≤ (x ^ 2)⁻¹ := by positivity
      calc
        |(-((x ^ 2)⁻¹) * (-Real.cos x))| = |(x ^ 2)⁻¹| * |Real.cos x| := by
          simp [abs_mul]
        _ ≤ |(x ^ 2)⁻¹| * 1 := by gcongr; exact abs_cos_le_one x
        _ = (x ^ 2)⁻¹ := by simp [abs_of_nonneg hx_inv_nonneg]
    calc
      |∫ x in s..t, -((x ^ 2)⁻¹) * (-Real.cos x)|
          ≤ ∫ x in s..t, |(-((x ^ 2)⁻¹) * (-Real.cos x))| :=
        intervalIntegral.abs_integral_le_integral_abs hst
      _ ≤ ∫ x in s..t, (x ^ 2)⁻¹ :=
        intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hst h_int_abs h_int_rhs h_point
  have h_inv_le : t⁻¹ ≤ s⁻¹ := (inv_le_inv₀ ht_pos hs_pos).2 hst
  have h_inv_sq_bound : ∫ x in s..t, (x ^ 2)⁻¹ ≤ s⁻¹ := by
    calc
      ∫ x in s..t, (x ^ 2)⁻¹ = s⁻¹ - t⁻¹ := h_inv_sq_int
      _ ≤ s⁻¹ := by nlinarith [inv_nonneg.mpr ht_pos.le]
  calc
    |∫ x in s..t, _root_.sinc x|
        = |t⁻¹ * (-Real.cos t) - s⁻¹ * (-Real.cos s)
            - ∫ x in s..t, -((x ^ 2)⁻¹) * (-Real.cos x)| := by
            rw [hsinc_eq, hparts]
    _ ≤ |t⁻¹ * (-Real.cos t) - s⁻¹ * (-Real.cos s)| +
          |∫ x in s..t, -((x ^ 2)⁻¹) * (-Real.cos x)| := by
            simpa using
              (abs_sub (t⁻¹ * (-Real.cos t) - s⁻¹ * (-Real.cos s))
                (∫ x in s..t, -((x ^ 2)⁻¹) * (-Real.cos x)))
    _ ≤ (|t⁻¹ * (-Real.cos t)| + |s⁻¹ * (-Real.cos s)|) + ∫ x in s..t, (x ^ 2)⁻¹ := by
      have hsub :
          |t⁻¹ * (-Real.cos t) - s⁻¹ * (-Real.cos s)| ≤
            |t⁻¹ * (-Real.cos t)| + |s⁻¹ * (-Real.cos s)| := by
          simpa using (abs_sub (t⁻¹ * (-Real.cos t)) (s⁻¹ * (-Real.cos s)))
      linarith [hsub, h_rem_int]
    _ ≤ (t⁻¹ + s⁻¹) + s⁻¹ := by
      linarith [h_term1, h_term2, h_inv_sq_bound]
    _ ≤ (3 : ℝ) * s⁻¹ := by nlinarith [h_inv_le]
    _ = 3 / s := by simp [div_eq_mul_inv]

/-- The primitive `t ↦ ∫_0^t sinc` has a finite limit at `+∞`. -/
lemma sinc_primitive_tendsto_atTop_exists :
    ∃ L : ℝ, Tendsto (fun t : ℝ => ∫ x in (0 : ℝ)..t, _root_.sinc x) atTop (nhds L) := by
  let F : ℝ → ℝ := fun t => ∫ x in (0 : ℝ)..t, _root_.sinc x
  have hInt : ∀ a b : ℝ, IntervalIntegrable _root_.sinc MeasureTheory.volume a b := by
    intro a b
    simpa using (Real.continuous_sinc.intervalIntegrable a b)
  have hCauchy : Cauchy (Filter.map F atTop) := by
    rw [Metric.cauchy_iff]
    refine ⟨(Filter.map_neBot_iff F).2 atTop_neBot, ?_⟩
    intro ε hε
    let N : ℝ := max 1 (3 / ε)
    refine ⟨F '' Set.Ioi N, ?_, ?_⟩
    · change F ⁻¹' (F '' Set.Ioi N) ∈ atTop
      refine Filter.mem_of_superset (Ioi_mem_atTop N) ?_
      intro x hx
      exact ⟨x, hx, rfl⟩
    · intro u hu v hv
      rcases hu with ⟨x, hx, rfl⟩
      rcases hv with ⟨y, hy, rfl⟩
      have hmin_gt : N < min x y := lt_min hx hy
      have hmin_ge_one : (1 : ℝ) ≤ min x y := le_trans (le_max_left 1 (3 / ε)) hmin_gt.le
      have htail_xy : |∫ z in y..x, _root_.sinc z| ≤ 3 / (min x y) := by
        by_cases hyx : y ≤ x
        · have hy_one : (1 : ℝ) ≤ y := le_trans (le_max_left 1 (3 / ε)) hy.le
          have htail : |∫ z in y..x, _root_.sinc z| ≤ 3 / y := sinc_tail_bound hy_one hyx
          simpa [min_eq_right hyx] using htail
        · have hxy : x ≤ y := le_of_lt (lt_of_not_ge hyx)
          have hx_one : (1 : ℝ) ≤ x := le_trans (le_max_left 1 (3 / ε)) hx.le
          have htail : |∫ z in x..y, _root_.sinc z| ≤ 3 / x := sinc_tail_bound hx_one hxy
          have hsymm : |∫ z in y..x, _root_.sinc z| = |∫ z in x..y, _root_.sinc z| := by
            rw [intervalIntegral.integral_symm, abs_neg]
          simpa [hsymm, min_eq_left hxy] using htail
      have hdist_le : dist (F x) (F y) ≤ 3 / (min x y) := by
        have hdiff :
            F x - F y = ∫ z in y..x, _root_.sinc z := by
          simpa [F] using
            (intervalIntegral.integral_interval_sub_left
              (a := (0 : ℝ)) (b := x) (c := y) (hInt 0 x) (hInt 0 y))
        calc
          dist (F x) (F y) = |F x - F y| := by rw [Real.dist_eq]
          _ = |∫ z in y..x, _root_.sinc z| := by rw [hdiff]
          _ ≤ 3 / (min x y) := htail_xy
      have hthree_over_eps_lt : 3 / ε < min x y :=
        lt_of_le_of_lt (le_max_right 1 (3 / ε)) hmin_gt
      have hmin_pos : 0 < min x y := lt_of_lt_of_le zero_lt_one hmin_ge_one
      have hbound : 3 / (min x y) < ε := by
        have hmul : 3 < min x y * ε := (div_lt_iff₀ hε).1 hthree_over_eps_lt
        exact (div_lt_iff₀ hmin_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
      exact lt_of_le_of_lt hdist_le hbound
  letI : (atTop : Filter ℝ).NeBot := atTop_neBot
  exact (cauchy_map_iff_exists_tendsto (l := atTop) (f := F)).1 hCauchy

/-- Integral representation `sinc x = ∫_0^1 cos (t x) dt`. -/
lemma sinc_eq_integral_cos_mul (x : ℝ) :
    _root_.sinc x = ∫ t in (0 : ℝ)..1, Real.cos (t * x) := by
  by_cases hx : x = 0
  · subst hx
    simp [_root_.sinc]
  · have hmul :
      ∫ t in (0 : ℝ)..1, Real.cos (t * x)
        = x⁻¹ * ∫ u in (0 : ℝ)..x, Real.cos u := by
      simpa [zero_mul, one_mul] using
        (intervalIntegral.integral_comp_mul_right (f := Real.cos) (a := (0 : ℝ)) (b := 1)
          (c := x) hx)
    calc
      _root_.sinc x = Real.sin x / x := by simp [_root_.sinc, hx]
      _ = x⁻¹ * ∫ u in (0 : ℝ)..x, Real.cos u := by
        rw [integral_cos, Real.sin_zero, sub_zero, div_eq_mul_inv, mul_comm]
      _ = ∫ t in (0 : ℝ)..1, Real.cos (t * x) := by
        rw [hmul]

noncomputable def muA (a : ℝ) : MeasureTheory.Measure ℝ :=
  (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun x : ℝ => ENNReal.ofReal (Real.exp (-a * x)))

lemma charFun_muA (a t : ℝ) (ha : 0 < a) :
    MeasureTheory.charFun (muA a) t = (1 : ℂ) / (a - t * Complex.I) := by
  rw [MeasureTheory.charFun_apply_real, muA]
  rw [integral_withDensity_eq_integral_toReal_smul]
  · have hrew :
      (fun x : ℝ => ((ENNReal.ofReal (Real.exp (-a * x))).toReal : ℝ) •
          Complex.exp ((t * x) * Complex.I))
        =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
          (fun x : ℝ => Complex.exp (((-(a : ℂ)) + t * Complex.I) * x)) := by
      refine Filter.Eventually.of_forall ?_
      intro x
      have hcoef : ((ENNReal.ofReal (Real.exp (-a * x))).toReal : ℝ) = Real.exp (-a * x) :=
        ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))
      calc
        ((ENNReal.ofReal (Real.exp (-a * x))).toReal : ℝ) • Complex.exp ((t * x) * Complex.I)
            = (Real.exp (-a * x)) • Complex.exp ((t * x) * Complex.I) := by rw [hcoef]
        _ = ((Real.exp (-a * x) : ℂ)) * Complex.exp ((t * x) * Complex.I) := by simp
        _ = (Complex.exp (((-(a : ℂ)) * x))) * Complex.exp ((t * x) * Complex.I) := by
              have harg : ((-(a : ℂ)) * x) = ((-(a * x) : ℝ) : ℂ) := by norm_num
              rw [harg]
              simpa using (Complex.ofReal_exp (-(a * x))).symm
        _ = Complex.exp (((-(a : ℂ)) * x) + ((t * x) * Complex.I)) := by rw [← Complex.exp_add]
        _ = Complex.exp (((-(a : ℂ)) + t * Complex.I) * x) := by ring
    have hIoi :
        ∫ x : ℝ in Set.Ioi (0 : ℝ), Complex.exp (((-(a : ℂ)) + t * Complex.I) * x)
          = -Complex.exp (((-(a : ℂ)) + t * Complex.I) * 0) / ((-(a : ℂ)) + t * Complex.I) := by
      simpa using integral_exp_mul_complex_Ioi (a := (-(a : ℂ) + t * Complex.I))
        (by
          simpa [Complex.add_re, Complex.neg_re, Complex.mul_re, ha] using
            (show -(a : ℝ) < 0 by linarith)) 0
    rw [MeasureTheory.integral_congr_ae hrew]
    calc
      ∫ x : ℝ in Set.Ioi (0 : ℝ), Complex.exp (((-(a : ℂ)) + t * Complex.I) * x)
          = -Complex.exp (((-(a : ℂ)) + t * Complex.I) * 0) / ((-(a : ℂ)) + t * Complex.I) := hIoi
      _ = -(((-(a : ℂ)) + t * Complex.I)⁻¹) := by simp [div_eq_mul_inv, mul_comm]
      _ = (a - t * Complex.I)⁻¹ := by
        have hden : ((-(a : ℂ)) + t * Complex.I) = -(a - t * Complex.I) := by ring
        rw [hden, inv_neg, neg_neg]
      _ = (1 : ℂ) / (a - t * Complex.I) := by simp [one_div]
  · fun_prop
  · have hInt : MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (-a * x)) (Set.Ioi 0) :=
      integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0
    simpa [mul_comm, mul_left_comm, mul_assoc] using hInt.lintegral_lt_top

lemma damped_sinc_integral_eq_arctan (a : ℝ) (ha : 0 < a) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-a * x) * Real.sinc x) = Real.arctan (a⁻¹) := by
  have hIntExp : MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (-a * x)) (Set.Ioi 0) :=
      integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0
  have hlin :
      (∫⁻ x, ENNReal.ofReal (Real.exp (-a * x)) ∂ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) < ⊤ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hIntExp.lintegral_lt_top
  letI : MeasureTheory.IsFiniteMeasure (muA a) := by
    refine ⟨?_⟩
    show (muA a) Set.univ < ⊤
    rw [muA, MeasureTheory.withDensity_apply _ MeasurableSet.univ]
    simpa using hlin
  have hchar :
      ∫ t in (-1 : ℝ)..1, MeasureTheory.charFun (muA a) t
        = 2 * (1 : ℂ) * ↑(∫ x, Real.sinc (1 * x) ∂ (muA a)) := by
    simpa using (MeasureTheory.integral_charFun_Icc (μ := muA a) (r := (1 : ℝ)) (by positivity))
  have hcharEq :
      ∫ t in (-1 : ℝ)..1, (1 : ℂ) / (a - t * Complex.I)
        = 2 * (1 : ℂ) * ↑(∫ x, Real.sinc (1 * x) ∂ (muA a)) := by
    calc
      ∫ t in (-1 : ℝ)..1, (1 : ℂ) / (a - t * Complex.I)
          = ∫ t in (-1 : ℝ)..1, MeasureTheory.charFun (muA a) t := by
              refine intervalIntegral.integral_congr ?_
              intro t ht
              simpa using (charFun_muA a t ha).symm
      _ = 2 * (1 : ℂ) * ↑(∫ x, Real.sinc (1 * x) ∂ (muA a)) := hchar
  have hEqRe := congrArg Complex.re hcharEq
  have hLHS :
      Complex.re (∫ t in (-1 : ℝ)..1, (1 : ℂ) / (a - t * Complex.I))
        = 2 * Real.arctan (a⁻¹) := by
    have hden_ne : ∀ t : ℝ, (a - t * Complex.I : ℂ) ≠ 0 := by
      intro t h0
      have hRe : a = 0 := by
        simpa [Complex.sub_re, Complex.mul_re] using congrArg Complex.re h0
      exact ha.ne' hRe
    have hInt : IntervalIntegrable (fun t : ℝ => (1 : ℂ) / (a - t * Complex.I)) MeasureTheory.volume (-1) 1 := by
      have hcont_den : Continuous (fun t : ℝ => (a - t * Complex.I : ℂ)) := by
        fun_prop
      have hcont_inv : Continuous (fun t : ℝ => (a - t * Complex.I : ℂ)⁻¹) :=
        hcont_den.inv₀ hden_ne
      have hcont : Continuous (fun t : ℝ => (1 : ℂ) / (a - t * Complex.I)) := by
        simpa [one_div] using hcont_inv
      exact hcont.intervalIntegrable (-1) 1
    have hReComm :
        (∫ t in (-1 : ℝ)..1, Complex.re ((1 : ℂ) / (a - t * Complex.I)))
          = Complex.re (∫ t in (-1 : ℝ)..1, (1 : ℂ) / (a - t * Complex.I)) := by
      simpa using (ContinuousLinearMap.intervalIntegral_comp_comm (μ := MeasureTheory.volume)
        (a := (-1 : ℝ)) (b := (1 : ℝ)) (L := Complex.reCLM)
        (f := fun t : ℝ => (1 : ℂ) / (a - t * Complex.I)) hInt)
    have hcore :
        (∫ t in (-1 : ℝ)..1, Complex.re ((1 : ℂ) / (a - t * Complex.I)))
          = 2 * Real.arctan (a⁻¹) := by
      have hform :
          (fun t : ℝ => Complex.re ((1 : ℂ) / (a - t * Complex.I)))
            = fun t : ℝ => a / (a ^ 2 + t ^ 2) := by
        funext t
        calc
          Complex.re ((1 : ℂ) / (a - t * Complex.I))
              = Complex.re ((a - t * Complex.I)⁻¹) := by simp [one_div]
          _ = (a - t * Complex.I).re / Complex.normSq (a - t * Complex.I) := by rw [Complex.inv_re]
          _ = a / (a ^ 2 + t ^ 2) := by simp [Complex.normSq, pow_two]
      rw [hform]
      have ha0 : a ≠ 0 := ne_of_gt ha
      have hEqIntegrand :
          (fun t : ℝ => a / (a ^ 2 + t ^ 2)) =
            fun t : ℝ => a⁻¹ * (1 + (t / a) ^ 2)⁻¹ := by
        funext t
        field_simp [ha0]
      rw [hEqIntegrand]
      rw [intervalIntegral.integral_const_mul]
      have hsub :
          a⁻¹ * (∫ t in (-1 : ℝ)..1, (1 + (t / a) ^ 2)⁻¹)
            = ∫ u in (-1 : ℝ) / a..(1 : ℝ) / a, (1 + u ^ 2)⁻¹ := by
        exact (intervalIntegral.inv_mul_integral_comp_div
          (f := fun u : ℝ => (1 + u ^ 2)⁻¹) (a := (-1 : ℝ)) (b := (1 : ℝ)) (c := a))
      have hInt2 :
          (∫ u in (-1 : ℝ) / a..(1 : ℝ) / a, (1 + u ^ 2)⁻¹)
            = Real.arctan ((1 : ℝ) / a) - Real.arctan ((-1 : ℝ) / a) := by
        simpa using (integral_inv_one_add_sq (a := (-1 : ℝ) / a) (b := (1 : ℝ) / a))
      have hfinal :
          Real.arctan ((1 : ℝ) / a) - Real.arctan ((-1 : ℝ) / a) = 2 * Real.arctan (a⁻¹) := by
        have h1 : ((1 : ℝ) / a) = a⁻¹ := by simp [one_div]
        have h2 : ((-1 : ℝ) / a) = -a⁻¹ := by field_simp [ha0]
        rw [h1, h2, Real.arctan_neg]
        ring
      calc
        a⁻¹ * (∫ t in (-1 : ℝ)..1, (1 + (t / a) ^ 2)⁻¹)
            = ∫ u in (-1 : ℝ) / a..(1 : ℝ) / a, (1 + u ^ 2)⁻¹ := hsub
        _ = Real.arctan ((1 : ℝ) / a) - Real.arctan ((-1 : ℝ) / a) := hInt2
        _ = 2 * Real.arctan (a⁻¹) := hfinal
    calc
      Complex.re (∫ t in (-1 : ℝ)..1, (1 : ℂ) / (a - t * Complex.I))
        = (∫ t in (-1 : ℝ)..1, Complex.re ((1 : ℂ) / (a - t * Complex.I))) := by
            symm
            exact hReComm
      _ = 2 * Real.arctan (a⁻¹) := hcore
  have hRHS :
      Complex.re (2 * (1 : ℂ) * ↑(∫ x, Real.sinc (1 * x) ∂ (muA a)))
        = 2 * (∫ x, Real.sinc (1 * x) ∂ (muA a)) := by
    norm_num
  have hMuVal : (∫ x, Real.sinc (1 * x) ∂ (muA a)) = Real.arctan (a⁻¹) := by
    have : 2 * Real.arctan (a⁻¹) = 2 * (∫ x, Real.sinc (1 * x) ∂ (muA a)) := by
      calc
        2 * Real.arctan (a⁻¹)
            = Complex.re (∫ t in (-1 : ℝ)..1, (1 : ℂ) / (a - t * Complex.I)) := by
                symm
                exact hLHS
        _ = Complex.re (2 * (1 : ℂ) * ↑(∫ x, Real.sinc (1 * x) ∂ (muA a))) := hEqRe
        _ = 2 * (∫ x, Real.sinc (1 * x) ∂ (muA a)) := hRHS
    linarith
  have hMuRewrite :
      (∫ x, Real.sinc (1 * x) ∂ (muA a))
        = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-a * x) * Real.sinc (1 * x) := by
    rw [muA, integral_withDensity_eq_integral_toReal_smul]
    · refine MeasureTheory.integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      change ((ENNReal.ofReal (Real.exp (-a * x))).toReal : ℝ) • Real.sinc (1 * x) =
        Real.exp (-a * x) * Real.sinc (1 * x)
      have hcoef : ((ENNReal.ofReal (Real.exp (-a * x))).toReal : ℝ) = Real.exp (-a * x) :=
        ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))
      rw [hcoef]
      simp [smul_eq_mul]
    · fun_prop
    · simpa using hlin
  calc
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-a * x) * Real.sinc x
        = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-a * x) * Real.sinc (1 * x) := by simp
    _ = (∫ x, Real.sinc (1 * x) ∂ (muA a)) := by rw [hMuRewrite]
    _ = Real.arctan (a⁻¹) := hMuVal

lemma integrableOn_exp_mul_comp_of_tendsto
    (F : ℝ → ℝ) (hFcont : Continuous F) {L : ℝ} (hL : Tendsto F atTop (nhds L))
    (a : ℝ) (ha : 0 ≤ a) :
    MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (-x) * F (a * x)) (Set.Ioi (0 : ℝ)) := by
  have hnear : ∀ᶠ x : ℝ in atTop, |F x - L| < 1 := by
    simpa [Real.dist_eq] using hL.eventually (Metric.ball_mem_nhds L zero_lt_one)
  rcases (eventually_atTop.1 hnear) with ⟨N, hN⟩
  let N0 : ℝ := max N 0
  have hN0_nonneg : 0 ≤ N0 := by simp [N0]
  have hN_le_N0 : N ≤ N0 := by simp [N0]
  obtain ⟨C0, hC0⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) N0)).exists_bound_of_continuousOn
      (hFcont.continuousOn)
  let M : ℝ := max C0 (|L| + 1)
  have hF_bound_nonneg : ∀ y : ℝ, 0 ≤ y → |F y| ≤ M := by
    intro y hy
    by_cases hyN0 : y ≤ N0
    · have hyIcc : y ∈ Set.Icc (0 : ℝ) N0 := ⟨hy, hyN0⟩
      have hC0y : ‖F y‖ ≤ C0 := hC0 y hyIcc
      have : |F y| ≤ C0 := by simpa [Real.norm_eq_abs] using hC0y
      exact this.trans (le_max_left _ _)
    · have hyN : N ≤ y := le_trans hN_le_N0 (le_of_not_ge hyN0)
      have hNy : |F y - L| < 1 := hN y hyN
      have htri : |F y| ≤ |F y - L| + |L| := by
        have := norm_add_le (F y - L) L
        simpa [Real.norm_eq_abs, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
      have htail : |F y| ≤ |L| + 1 := by linarith
      exact htail.trans (le_max_right _ _)
  have hExpInt : MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi 0) := by
    simpa [mul_comm] using (integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0)
  have hbound_int : MeasureTheory.IntegrableOn (fun x : ℝ => M * Real.exp (-x)) (Set.Ioi (0 : ℝ)) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hExpInt.const_mul M
  have hcontFn : Continuous (fun x : ℝ => Real.exp (-x) * F (a * x)) := by
    refine (Real.continuous_exp.comp (continuous_id.neg)).mul ?_
    exact hFcont.comp (continuous_const.mul continuous_id)
  refine hbound_int.mono' hcontFn.aestronglyMeasurable ?_
  refine MeasureTheory.ae_restrict_of_forall_mem (μ := MeasureTheory.volume) measurableSet_Ioi ?_
  intro x hx
  have hx_nonneg : 0 ≤ x := le_of_lt hx
  have harg_nonneg : 0 ≤ a * x := mul_nonneg ha hx_nonneg
  have hFbx : |F (a * x)| ≤ M := hF_bound_nonneg (a * x) harg_nonneg
  have hexp_nonneg : 0 ≤ Real.exp (-x) := le_of_lt (Real.exp_pos _)
  have hmul : |Real.exp (-x) * F (a * x)| ≤ M * Real.exp (-x) := by
    calc
      |Real.exp (-x) * F (a * x)|
          = Real.exp (-x) * |F (a * x)| := by
              simp [abs_mul, abs_of_nonneg hexp_nonneg]
      _ ≤ Real.exp (-x) * M := by gcongr
      _ = M * Real.exp (-x) := by ring
  simpa [Real.norm_eq_abs] using hmul

lemma abel_weighted_tendsto_of_tendsto (F : ℝ → ℝ) (L : ℝ)
    (hFcont : Continuous F) (hL : Tendsto F atTop (nhds L)) :
    Tendsto (fun n : ℕ => ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F (((n : ℝ) + 1) * x))
      atTop (nhds L) := by
  have hnear : ∀ᶠ x : ℝ in atTop, |F x - L| < 1 := by
    simpa [Real.dist_eq] using hL.eventually (Metric.ball_mem_nhds L zero_lt_one)
  rcases (eventually_atTop.1 hnear) with ⟨N, hN⟩
  let N0 : ℝ := max N 0
  have hN0_nonneg : 0 ≤ N0 := by simp [N0]
  have hN_le_N0 : N ≤ N0 := by simp [N0]
  obtain ⟨C0, hC0⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) N0)).exists_bound_of_continuousOn
      (hFcont.continuousOn)
  let M : ℝ := max C0 (|L| + 1)
  have hF_bound_nonneg : ∀ y : ℝ, 0 ≤ y → |F y| ≤ M := by
    intro y hy
    by_cases hyN0 : y ≤ N0
    · have hyIcc : y ∈ Set.Icc (0 : ℝ) N0 := ⟨hy, hyN0⟩
      have hC0y : ‖F y‖ ≤ C0 := hC0 y hyIcc
      have : |F y| ≤ C0 := by simpa [Real.norm_eq_abs] using hC0y
      exact this.trans (le_max_left _ _)
    · have hyN : N ≤ y := le_trans hN_le_N0 (le_of_not_ge hyN0)
      have hNy : |F y - L| < 1 := hN y hyN
      have htri : |F y| ≤ |F y - L| + |L| := by
        have := norm_add_le (F y - L) L
        simpa [Real.norm_eq_abs, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
      have htail : |F y| ≤ |L| + 1 := by linarith
      exact htail.trans (le_max_right _ _)
  have hbound_int : MeasureTheory.IntegrableOn (fun x : ℝ => M * Real.exp (-x)) (Set.Ioi (0 : ℝ)) := by
    have hExpInt : MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi 0) :=
      by simpa [mul_comm] using (integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hExpInt.const_mul M
  have hDom :
      Tendsto (fun n : ℕ => ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F (((n : ℝ) + 1) * x))
        atTop (nhds (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * L)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (F := fun n x => Real.exp (-x) * F (((n : ℝ) + 1) * x))
      (f := fun x => Real.exp (-x) * L)
      (bound := fun x => M * Real.exp (-x)) ?meas ?boundInt ?bound ?lim
    · intro n
      have hcontFn :
          Continuous (fun x : ℝ => Real.exp (-x) * F (((n : ℝ) + 1) * x)) := by
        refine (Real.continuous_exp.comp (continuous_id.neg)).mul ?_
        exact hFcont.comp (continuous_const.mul continuous_id)
      exact hcontFn.aestronglyMeasurable
    · simpa using hbound_int
    · intro n
      refine MeasureTheory.ae_restrict_of_forall_mem (μ := MeasureTheory.volume) measurableSet_Ioi ?_
      intro x hx
      have hx_nonneg : 0 ≤ x := le_of_lt hx
      have harg_nonneg : 0 ≤ (((n : ℝ) + 1) * x) := by positivity
      have hFbx : |F (((n : ℝ) + 1) * x)| ≤ M := hF_bound_nonneg (((n : ℝ) + 1) * x) harg_nonneg
      have hexp_nonneg : 0 ≤ Real.exp (-x) := le_of_lt (Real.exp_pos _)
      have hmul : |Real.exp (-x) * F (((n : ℝ) + 1) * x)| ≤ M * Real.exp (-x) := by
        calc
          |Real.exp (-x) * F (((n : ℝ) + 1) * x)|
              = Real.exp (-x) * |F (((n : ℝ) + 1) * x)| := by
                  simp [abs_mul, abs_of_nonneg hexp_nonneg]
          _ ≤ Real.exp (-x) * M := by gcongr
          _ = M * Real.exp (-x) := by ring
      simpa [Real.norm_eq_abs] using hmul
    · refine MeasureTheory.ae_restrict_of_forall_mem (μ := MeasureTheory.volume) measurableSet_Ioi ?_
      intro x hx
      have hx_pos : 0 < x := hx
      have hNatMul : Tendsto (fun n : ℕ => (n : ℝ) * x) atTop atTop := by
        exact tendsto_natCast_atTop_atTop.atTop_mul_const hx_pos
      have hShift : Tendsto (fun n : ℕ => (n : ℝ) * x + x) atTop atTop :=
        Filter.tendsto_atTop_add_const_right atTop x hNatMul
      have hx_tend : Tendsto (fun n : ℕ => (((n : ℝ) + 1) * x)) atTop atTop := by
        have hEq : (fun n : ℕ => (((n : ℝ) + 1) * x)) = (fun n : ℕ => (n : ℝ) * x + x) := by
          funext n
          ring
        exact hShift.congr' (Filter.EventuallyEq.of_eq hEq.symm)
      have hFtend : Tendsto (fun n : ℕ => F ((((n : ℝ) + 1) * x))) atTop (nhds L) :=
        hL.comp hx_tend
      exact (tendsto_const_nhds.mul hFtend)
  have hIntL : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * L) = L := by
    have hExpOne : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x)) = 1 := by
      simpa using integral_exp_neg_Ioi_zero
    calc
      ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * L
          = (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x)) * L := by
              simpa using (MeasureTheory.integral_mul_const (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                (r := L) (f := fun x : ℝ => Real.exp (-x)))
      _ = L := by simpa [hExpOne]
  simpa [hIntL] using hDom

lemma weighted_primitive_eval
    (F : ℝ → ℝ) (hF0 : F 0 = 0)
    (hFderiv : ∀ x : ℝ, HasDerivAt F (Real.sinc x) x)
    {L : ℝ} (hL : Tendsto F atTop (nhds L)) (n : ℕ) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F (((n : ℝ) + 1) * x))
      = Real.arctan ((n : ℝ) + 1) := by
  let α : ℝ := (n : ℝ) + 1
  have hα : 0 < α := by
    dsimp [α]
    positivity
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hFcont : Continuous F := by
    refine continuous_iff_continuousAt.2 ?_
    intro x
    exact (hFderiv x).continuousAt
  have hIntLeft : MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (-x) * F (α * x)) (Set.Ioi 0) :=
    integrableOn_exp_mul_comp_of_tendsto F hFcont hL α hα.le
  have hExpInt : MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi 0) := by
    simpa [mul_comm] using (integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0)
  have hIntSincBase :
      MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (-x) * Real.sinc (α * x)) (Set.Ioi 0) := by
    refine hExpInt.mono' ?_ ?_
    · have hcont : Continuous (fun x : ℝ => Real.exp (-x) * Real.sinc (α * x)) := by
        refine (Real.continuous_exp.comp (continuous_id.neg)).mul ?_
        exact Real.continuous_sinc.comp (continuous_const.mul continuous_id)
      exact hcont.aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem (μ := MeasureTheory.volume) measurableSet_Ioi ?_
      intro x hx
      have hexp_nonneg : 0 ≤ Real.exp (-x) := le_of_lt (Real.exp_pos _)
      have hmul : |Real.exp (-x) * Real.sinc (α * x)| ≤ Real.exp (-x) := by
        calc
          |Real.exp (-x) * Real.sinc (α * x)|
              = Real.exp (-x) * |Real.sinc (α * x)| := by
                  simp [abs_mul, abs_of_nonneg hexp_nonneg]
          _ ≤ Real.exp (-x) * 1 := by
                gcongr
                exact Real.abs_sinc_le_one (α * x)
          _ = Real.exp (-x) := by ring
      simpa [Real.norm_eq_abs] using hmul
  have hIntA :
      MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (-x) * (α * Real.sinc (α * x))) (Set.Ioi 0) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hIntSincBase.const_mul α
  have hIntDeriv :
      MeasureTheory.IntegrableOn
        (fun x : ℝ => Real.exp (-x) * (α * Real.sinc (α * x) - F (α * x))) (Set.Ioi 0) := by
    have hSub :
        MeasureTheory.IntegrableOn
          (fun x : ℝ => Real.exp (-x) * (α * Real.sinc (α * x)) - Real.exp (-x) * F (α * x))
          (Set.Ioi 0) :=
      hIntA.sub hIntLeft
    refine (MeasureTheory.integrableOn_congr_fun ?_ measurableSet_Ioi).2 hSub
    intro x hx
    ring
  have hScale : Tendsto (fun x : ℝ => α * x) atTop atTop := by
    have h : Tendsto (fun x : ℝ => x * α) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hα tendsto_id
    simpa [mul_comm] using h
  have hFScale : Tendsto (fun x : ℝ => F (α * x)) atTop (nhds L) :=
    hL.comp hScale
  have hExp0 : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (nhds (0 : ℝ)) := by
    change Tendsto (Real.exp ∘ Neg.neg) atTop (nhds (0 : ℝ))
    exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hLimG : Tendsto (fun x : ℝ => Real.exp (-x) * F (α * x)) atTop (nhds (0 : ℝ)) := by
    have h := hExp0.mul hFScale
    simpa using h
  have hDeriv :
      ∀ x ∈ Set.Ici (0 : ℝ),
        HasDerivAt (fun y : ℝ => Real.exp (-y) * F (α * y))
          (Real.exp (-x) * (α * Real.sinc (α * x) - F (α * x))) x := by
    intro x hx
    have hExpDeriv : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
      simpa using (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    have hFScaleDeriv : HasDerivAt (fun y : ℝ => F (α * y)) (α * Real.sinc (α * x)) x := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (hFderiv (x * α)).comp x (hasDerivAt_mul_const (x := x) α)
    convert hExpDeriv.mul hFScaleDeriv using 1 <;> ring
  have hDerivIntEq :
      ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * (α * Real.sinc (α * x) - F (α * x)) = 0 := by
    have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (f := fun y : ℝ => Real.exp (-y) * F (α * y))
      (f' := fun x : ℝ => Real.exp (-x) * (α * Real.sinc (α * x) - F (α * x)))
      (a := 0) (m := (0 : ℝ)) hDeriv hIntDeriv hLimG
    simpa [hF0] using hFTC
  have hSubEq :
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * (α * Real.sinc (α * x)))
        - (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F (α * x)) = 0 := by
    have hSubInt :=
      MeasureTheory.integral_sub (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (f := fun x : ℝ => Real.exp (-x) * (α * Real.sinc (α * x)))
        (g := fun x : ℝ => Real.exp (-x) * F (α * x)) hIntA hIntLeft
    have hEqDeriv :
        (fun x : ℝ => Real.exp (-x) * (α * Real.sinc (α * x) - F (α * x))) =
          (fun x : ℝ => Real.exp (-x) * (α * Real.sinc (α * x)) - Real.exp (-x) * F (α * x)) := by
      funext x
      ring
    calc
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * (α * Real.sinc (α * x)))
          - (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F (α * x))
          = ∫ x in Set.Ioi (0 : ℝ),
              (Real.exp (-x) * (α * Real.sinc (α * x)) - Real.exp (-x) * F (α * x)) := by
                symm
                exact hSubInt
      _ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * (α * Real.sinc (α * x) - F (α * x)) := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.EventuallyEq.of_eq hEqDeriv.symm
      _ = 0 := hDerivIntEq
  have hEqAF :
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F (α * x))
        = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * (α * Real.sinc (α * x)) := by
    linarith
  have hEqAConst :
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * (α * Real.sinc (α * x)))
        = α * (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * Real.sinc (α * x)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (r := α) (f := fun x : ℝ => Real.exp (-x) * Real.sinc (α * x)))
  have hScaleSinc :
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * Real.sinc (α * x))
        = α⁻¹ * (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(α⁻¹) * u) * Real.sinc u) := by
    have hComp := MeasureTheory.integral_comp_mul_left_Ioi
      (g := fun u : ℝ => Real.exp (-(α⁻¹) * u) * Real.sinc u) (a := 0) (b := α) hα
    have hEqLeft :
        (fun x : ℝ => (Real.exp (-(α⁻¹) * (α * x)) * Real.sinc (α * x)))
          = (fun x : ℝ => Real.exp (-x) * Real.sinc (α * x)) := by
      funext x
      have hm : α⁻¹ * (α * x) = x := by field_simp [hα0]
      simp [hm]
    calc
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * Real.sinc (α * x))
          = (∫ x in Set.Ioi (0 : ℝ),
              (fun u : ℝ => Real.exp (-(α⁻¹) * u) * Real.sinc u) (α * x)) := by
                refine MeasureTheory.integral_congr_ae ?_
                exact Filter.EventuallyEq.of_eq hEqLeft.symm
      _ = α⁻¹ • ∫ x in Set.Ioi (α * (0 : ℝ)),
            (fun u : ℝ => Real.exp (-(α⁻¹) * u) * Real.sinc u) x := hComp
      _ = α⁻¹ * (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(α⁻¹) * u) * Real.sinc u) := by
            simp [smul_eq_mul]
  have hAlphaMul :
      α * (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * Real.sinc (α * x))
        = (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(α⁻¹) * u) * Real.sinc u) := by
    calc
      α * (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * Real.sinc (α * x))
          = α * (α⁻¹ * (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(α⁻¹) * u) * Real.sinc u)) := by
              rw [hScaleSinc]
      _ = (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(α⁻¹) * u) * Real.sinc u) := by
            field_simp [hα0]
  have hDamped :
      (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(α⁻¹) * u) * Real.sinc u) = Real.arctan α := by
    simpa [hα0] using (damped_sinc_integral_eq_arctan (a := α⁻¹) (inv_pos.mpr hα))
  calc
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F (((n : ℝ) + 1) * x))
        = (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F (α * x)) := by simp [α]
    _ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * (α * Real.sinc (α * x)) := hEqAF
    _ = α * (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * Real.sinc (α * x)) := hEqAConst
    _ = (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(α⁻¹) * u) * Real.sinc u) := hAlphaMul
    _ = Real.arctan α := hDamped
    _ = Real.arctan ((n : ℝ) + 1) := by simp [α]

/-- Example 5.5.12. The improper integral of the sinc function over the real
line converges and equals `π`, but the integral of its absolute value diverges,
so the convergence is not absolute. -/
theorem improperIntegral_sinc_conditional :
    ImproperIntegralRealLine _root_.sinc Real.pi ∧
      ¬ ∃ l : ℝ, ImproperIntegralRealLine (fun x : ℝ => |_root_.sinc x|) l := by
  refine ⟨?hconv, ?hnotAbs⟩
  · -- Classical Dirichlet-integral fact:
    -- `∫_{-∞}^{∞} sinc = π`, decomposed via
    -- `F(t) := ∫_0^t sinc`.
    have hsinc_eq_real : (_root_.sinc : ℝ → ℝ) = Real.sinc := rfl
    let F : ℝ → ℝ := fun t => ∫ x in (0 : ℝ)..t, _root_.sinc x
    have hInt : ∀ a b : ℝ, MeasureTheory.IntegrableOn _root_.sinc (Set.Icc a b) := by
      intro a b
      by_cases hab : a ≤ b
      · have hIntab : IntervalIntegrable _root_.sinc MeasureTheory.volume a b := by
          simpa [hsinc_eq_real] using Real.continuous_sinc.intervalIntegrable a b
        exact (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := MeasureTheory.volume) hab).1 hIntab
      · have hIcc : Set.Icc a b = (∅ : Set ℝ) := Icc_eq_empty hab
        simpa [hIcc] using (MeasureTheory.integrableOn_empty : MeasureTheory.IntegrableOn _root_.sinc (∅ : Set ℝ))
    have hF_neg : ∀ t : ℝ, F (-t) = -F t := by
      intro t
      have hsymm :
          (∫ x in (0 : ℝ)..t, _root_.sinc x) = ∫ x in (-t)..0, _root_.sinc x := by
        simpa [hsinc_eq_real] using
          (intervalIntegral.integral_comp_neg (f := Real.sinc) (a := (0 : ℝ)) (b := t))
      calc
        F (-t) = ∫ x in (0 : ℝ)..(-t), _root_.sinc x := rfl
        _ = -∫ x in (-t)..0, _root_.sinc x := by rw [intervalIntegral.integral_symm]
        _ = -∫ x in (0 : ℝ)..t, _root_.sinc x := by rw [← hsymm]
        _ = -F t := rfl
    have htop_base : Tendsto F atTop (nhds (Real.pi / 2)) := by
      have htop_exists : ∃ L : ℝ, Tendsto F atTop (nhds L) := by
        simpa [F] using sinc_primitive_tendsto_atTop_exists
      have htop_value :
          ∀ L : ℝ, Tendsto F atTop (nhds L) → L = Real.pi / 2 := by
        intro L hL
        -- Dirichlet integral value identification:
        -- `lim_{t→∞} ∫_0^t sinc = π/2`.
        have hF0 : F 0 = 0 := by
          simp [F]
        have hFderiv : ∀ x : ℝ, HasDerivAt F (Real.sinc x) x := by
          intro x
          have hInt : IntervalIntegrable Real.sinc MeasureTheory.volume (0 : ℝ) x := by
            simpa using Real.continuous_sinc.intervalIntegrable (0 : ℝ) x
          simpa [F, hsinc_eq_real] using
            (intervalIntegral.integral_hasDerivAt_right (f := Real.sinc) hInt
              (Real.continuous_sinc.stronglyMeasurableAtFilter
                (μ := MeasureTheory.volume) (l := nhds x))
              (Real.continuous_sinc.continuousAt))
        have hFcont : Continuous F := by
          refine continuous_iff_continuousAt.2 ?_
          intro x
          exact (hFderiv x).continuousAt
        have hSeqL :
            Tendsto (fun n : ℕ => ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F (((n : ℝ) + 1) * x))
              atTop (nhds L) :=
          abel_weighted_tendsto_of_tendsto F L hFcont hL
        have hSeqEq :
            ∀ n : ℕ,
              (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F (((n : ℝ) + 1) * x))
                = Real.arctan ((n : ℝ) + 1) := by
          intro n
          exact weighted_primitive_eval F hF0 hFderiv hL n
        have hArctanL :
            Tendsto (fun n : ℕ => Real.arctan ((n : ℝ) + 1)) atTop (nhds L) := by
          have hEqFun :
              (fun n : ℕ => ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F (((n : ℝ) + 1) * x))
                = (fun n : ℕ => Real.arctan ((n : ℝ) + 1)) := by
            funext n
            exact hSeqEq n
          exact hSeqL.congr' (Filter.EventuallyEq.of_eq hEqFun)
        have hShift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
          exact Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
        have hArctanPi :
            Tendsto (fun n : ℕ => Real.arctan ((n : ℝ) + 1)) atTop (nhds (Real.pi / 2)) := by
          exact (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp hShift
        exact tendsto_nhds_unique hArctanL hArctanPi
      rcases htop_exists with ⟨L, hL⟩
      have hLval : L = Real.pi / 2 := htop_value L hL
      simpa [hLval] using hL
    have hbot_base : Tendsto F atBot (nhds (-(Real.pi / 2))) := by
      have hcomp : Tendsto (fun t : ℝ => F (-t)) atBot (nhds (Real.pi / 2)) :=
        htop_base.comp tendsto_neg_atBot_atTop
      have hneg : Tendsto (fun t : ℝ => -F t) atBot (nhds (Real.pi / 2)) := by
        have hEq : (fun t : ℝ => F (-t)) = fun t => -F t := by
          funext t
          simpa using hF_neg t
        exact hcomp.congr' (Filter.EventuallyEq.of_eq hEq)
      simpa using hneg.neg
    have hprod :
        Tendsto (fun p : ℝ × ℝ => ∫ x in p.1..p.2, _root_.sinc x)
          (Filter.atBot ×ˢ Filter.atTop) (nhds (Real.pi : ℝ)) := by
      have htemp :=
        tendsto_intervalIntegral_atBot_atTop_of_base (f := _root_.sinc) hInt
          (hbot := by simpa [F] using hbot_base)
          (htop := by simpa [F] using htop_base)
      have hpi : (Real.pi / 2) - (-(Real.pi / 2)) = (Real.pi : ℝ) := by ring
      simpa [hpi] using htemp
    exact ⟨hInt, hprod⟩
  · intro hAbs
    rcases hAbs with ⟨l, hAbsInt, hAbsTendsto⟩
    have hsinc_eq_real : (_root_.sinc : ℝ → ℝ) = Real.sinc := rfl
    have habs_periodic : Function.Periodic (fun x : ℝ => |Real.sin x|) Real.pi := by
      intro x
      simp [Real.sin_add_pi]
    have habs_int_pi : (∫ x in (0 : ℝ)..Real.pi, |Real.sin x|) = (2 : ℝ) := by
      have hEq : EqOn (fun x : ℝ => |Real.sin x|) Real.sin (Set.uIcc (0 : ℝ) Real.pi) := by
        intro x hx
        have hx' : x ∈ Set.Icc (0 : ℝ) Real.pi := by
          simpa [Set.uIcc_of_le Real.pi_pos.le] using hx
        exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx'.1 hx'.2)
      calc
        ∫ x in (0 : ℝ)..Real.pi, |Real.sin x| = ∫ x in (0 : ℝ)..Real.pi, Real.sin x := by
          exact intervalIntegral.integral_congr hEq
        _ = Real.cos (0 : ℝ) - Real.cos Real.pi := by simpa using (integral_sin (a := (0 : ℝ)) (b := Real.pi))
        _ = (2 : ℝ) := by norm_num [Real.cos_zero, Real.cos_pi]
    have hblock_abs_sin : ∀ n : ℕ,
        (∫ x in ((n : ℝ) * Real.pi)..(((n : ℝ) + 1) * Real.pi), |Real.sin x|) = (2 : ℝ) := by
      intro n
      have hperiod :
          ∫ x in ((n : ℝ) * Real.pi)..((n : ℝ) * Real.pi + Real.pi), |Real.sin x|
            = ∫ x in (0 : ℝ)..((0 : ℝ) + Real.pi), |Real.sin x| := by
        simpa using habs_periodic.intervalIntegral_add_eq ((n : ℝ) * Real.pi) (0 : ℝ)
      have hright :
          ((n : ℝ) * Real.pi) + Real.pi = (((n : ℝ) + 1) * Real.pi) := by ring
      calc
        ∫ x in ((n : ℝ) * Real.pi)..(((n : ℝ) + 1) * Real.pi), |Real.sin x|
            = ∫ x in ((n : ℝ) * Real.pi)..((n : ℝ) * Real.pi + Real.pi), |Real.sin x| := by
              simp [hright]
        _ = ∫ x in (0 : ℝ)..((0 : ℝ) + Real.pi), |Real.sin x| := hperiod
        _ = (2 : ℝ) := by simpa [habs_int_pi]
    have hblock_lower_pos :
        ∀ n : ℕ, 1 ≤ n →
          (2 : ℝ) / (((n : ℝ) + 1) * Real.pi)
            ≤ ∫ x in ((n : ℝ) * Real.pi)..(((n : ℝ) + 1) * Real.pi), |_root_.sinc x| := by
      intro n hn
      have hpi_pos : 0 < Real.pi := Real.pi_pos
      have hMpos : 0 < (((n : ℝ) + 1) * Real.pi) := by
        positivity
      have hpoint :
          ∀ x ∈ Set.Icc ((n : ℝ) * Real.pi) (((n : ℝ) + 1) * Real.pi),
            |Real.sin x| / (((n : ℝ) + 1) * Real.pi) ≤ |_root_.sinc x| := by
        intro x hx
        have hx_pos : 0 < x := by
          have hnp : (0 : ℝ) < (n : ℝ) * Real.pi := by
            have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
            positivity
          exact lt_of_lt_of_le hnp hx.1
        have hx_le : x ≤ (((n : ℝ) + 1) * Real.pi) := hx.2
        have hinv : ((((n : ℝ) + 1) * Real.pi) : ℝ)⁻¹ ≤ x⁻¹ := by
          exact (inv_le_inv₀ hMpos hx_pos).2 hx_le
        have hmul :
            |Real.sin x| * ((((n : ℝ) + 1) * Real.pi) : ℝ)⁻¹ ≤ |Real.sin x| * x⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (abs_nonneg (Real.sin x))
        have hsinc :
            |_root_.sinc x| = |Real.sin x| * x⁻¹ := by
          have hxne : x ≠ 0 := ne_of_gt hx_pos
          simp [hsinc_eq_real, Real.sinc_of_ne_zero hxne, abs_of_pos hx_pos, div_eq_mul_inv]
        simpa [div_eq_mul_inv, hsinc] using hmul
      have hIntLeft :
          IntervalIntegrable (fun x : ℝ => |Real.sin x| / (((n : ℝ) + 1) * Real.pi))
            MeasureTheory.volume (((n : ℝ) * Real.pi)) ((((n : ℝ) + 1) * Real.pi)) := by
        refine Continuous.intervalIntegrable ?_ _ _
        continuity
      have hIntRight :
          IntervalIntegrable (fun x : ℝ => |_root_.sinc x|) MeasureTheory.volume (((n : ℝ) * Real.pi))
            ((((n : ℝ) + 1) * Real.pi)) := by
        simpa [hsinc_eq_real] using (Real.continuous_sinc.abs.intervalIntegrable
          (((n : ℝ) * Real.pi)) ((((n : ℝ) + 1) * Real.pi)))
      have hmono :
          (∫ x in ((n : ℝ) * Real.pi)..(((n : ℝ) + 1) * Real.pi),
              |Real.sin x| / (((n : ℝ) + 1) * Real.pi))
            ≤ ∫ x in ((n : ℝ) * Real.pi)..(((n : ℝ) + 1) * Real.pi), |_root_.sinc x| := by
        have hab : ((n : ℝ) * Real.pi) ≤ (((n : ℝ) + 1) * Real.pi) := by
          nlinarith [Real.pi_pos.le]
        exact intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab hIntLeft hIntRight
          (by intro x hx; exact hpoint x hx)
      have hconst :
          (∫ x in ((n : ℝ) * Real.pi)..(((n : ℝ) + 1) * Real.pi),
              |Real.sin x| / (((n : ℝ) + 1) * Real.pi))
            = (∫ x in ((n : ℝ) * Real.pi)..(((n : ℝ) + 1) * Real.pi), |Real.sin x|)
                / (((n : ℝ) + 1) * Real.pi) := by
        have hfun :
            (fun x : ℝ => |Real.sin x| / (((n : ℝ) + 1) * Real.pi))
              = (fun x : ℝ => |Real.sin x| * ((((n : ℝ) + 1) * Real.pi)⁻¹)) := by
          funext x
          simp [div_eq_mul_inv]
        rw [hfun, intervalIntegral.integral_mul_const]
        simp [div_eq_mul_inv]
      calc
        (2 : ℝ) / (((n : ℝ) + 1) * Real.pi)
            = (∫ x in ((n : ℝ) * Real.pi)..(((n : ℝ) + 1) * Real.pi), |Real.sin x|)
                / (((n : ℝ) + 1) * Real.pi) := by simp [hblock_abs_sin n]
        _ = (∫ x in ((n : ℝ) * Real.pi)..(((n : ℝ) + 1) * Real.pi),
              |Real.sin x| / (((n : ℝ) + 1) * Real.pi)) := by
              rw [hconst]
        _ ≤ ∫ x in ((n : ℝ) * Real.pi)..(((n : ℝ) + 1) * Real.pi), |_root_.sinc x| := hmono
    have hpath :
        Tendsto (fun a : ℝ => (-a, a)) atTop (Filter.atBot ×ˢ Filter.atTop) :=
      tendsto_neg_atTop_atBot.prodMk tendsto_id
    have hsymm_to_l :
        Tendsto (fun a : ℝ => ∫ x in (-a)..a, |_root_.sinc x|) atTop (nhds l) := by
      have hcomp := hAbsTendsto.comp hpath
      simpa using hcomp
    have hseq_to_l :
        Tendsto (fun n : ℕ => ∫ x in (-(((n : ℝ) + 1) * Real.pi))..(((n : ℝ) + 1) * Real.pi),
          |_root_.sinc x|) atTop (nhds l) := by
      have hnat_toTop : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.pi) atTop atTop := by
        have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
          exact (tendsto_add_const_atTop (1 : ℝ)).comp tendsto_natCast_atTop_atTop
        exact (Filter.tendsto_mul_const_atTop_of_pos Real.pi_pos).2 hnat
      exact hsymm_to_l.comp hnat_toTop
    have hharm :
        Tendsto (fun n : ℕ =>
            Finset.sum (Finset.range n) (fun i => (1 : ℝ) / ((i : ℝ) + 1))) atTop atTop := by
      simpa using tendsto_sum_range_one_div_nat_succ_atTop
    have hseq_lower :
        ∀ n : ℕ,
          Finset.sum (Finset.range n)
            (fun i => (2 : ℝ) / (Real.pi + (Real.pi + Real.pi * (i : ℝ))))
            ≤ ∫ x in (-(((n : ℝ) + 1) * Real.pi))..(((n : ℝ) + 1) * Real.pi), |_root_.sinc x| := by
      intro n
      let f : ℝ → ℝ := fun x => |_root_.sinc x|
      let A : ℝ := ((n : ℝ) + 1) * Real.pi
      have hInt : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b := by
        intro a b
        exact intervalIntegrable_of_integrableOn_Icc (f := f) hAbsInt a b
      have hsplit :=
        (intervalIntegral.integral_add_adjacent_intervals (hInt (-A) Real.pi) (hInt Real.pi A)).symm
      have hleft_nonneg : 0 ≤ ∫ x in (-A)..Real.pi, f x := by
        have hA_nonneg : 0 ≤ A := by
          have hpi : 0 ≤ Real.pi := Real.pi_pos.le
          positivity
        have hle : -A ≤ Real.pi := by
          have hneg : -A ≤ (0 : ℝ) := by linarith
          exact le_trans hneg Real.pi_pos.le
        exact intervalIntegral.integral_nonneg hle (by
          intro x hx
          exact abs_nonneg (_root_.sinc x))
      have htail_le : ∫ x in Real.pi..A, f x ≤ ∫ x in (-A)..A, f x := by
        linarith [hleft_nonneg, hsplit]
      let a : ℕ → ℝ := fun k => ((k : ℝ) + 1) * Real.pi
      have hsum_eq :
          Finset.sum (Finset.range n) (fun k => ∫ x in a k..a (k + 1), f x)
            = ∫ x in a 0..a n, f x := by
        exact intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume) (f := f)
          (by
            intro k hk
            exact hInt (a k) (a (k + 1)))
      have hsum_blocks :
          Finset.sum (Finset.range n)
            (fun k => ∫ x in (Real.pi + Real.pi * (k : ℝ))..(Real.pi + (Real.pi + Real.pi * (k : ℝ))), f x)
            = ∫ x in Real.pi..A, f x := by
        simpa [a, A, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm, mul_add,
          mul_assoc, mul_comm, mul_left_comm] using hsum_eq
      have hsum_le_blocks :
          Finset.sum (Finset.range n)
            (fun i => (2 : ℝ) / (Real.pi + (Real.pi + Real.pi * (i : ℝ))))
            ≤ Finset.sum (Finset.range n)
                (fun k => ∫ x in (Real.pi + Real.pi * (k : ℝ))..(Real.pi + (Real.pi + Real.pi * (k : ℝ))), f x) := by
        refine Finset.sum_le_sum ?_
        intro k hk
        have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        simpa [f, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm, mul_add,
          mul_assoc, mul_comm, mul_left_comm] using hblock_lower_pos (n := k + 1) hk1
      calc
        Finset.sum (Finset.range n)
          (fun i => (2 : ℝ) / (Real.pi + (Real.pi + Real.pi * (i : ℝ))))
            ≤ Finset.sum (Finset.range n)
                (fun k => ∫ x in (Real.pi + Real.pi * (k : ℝ))..(Real.pi + (Real.pi + Real.pi * (k : ℝ))), f x) :=
          hsum_le_blocks
        _ = ∫ x in Real.pi..A, f x := hsum_blocks
        _ ≤ ∫ x in (-A)..A, f x := htail_le
        _ = ∫ x in (-(((n : ℝ) + 1) * Real.pi))..(((n : ℝ) + 1) * Real.pi), |_root_.sinc x| := by
          simp [f, A]
    have hseq_atTop :
        Tendsto (fun n : ℕ => ∫ x in (-(((n : ℝ) + 1) * Real.pi))..(((n : ℝ) + 1) * Real.pi),
          |_root_.sinc x|) atTop atTop := by
      have hshift_harm :
          Tendsto (fun n : ℕ =>
              Finset.sum (Finset.range n) (fun i => (1 : ℝ) / ((i : ℝ) + 2))) atTop atTop := by
        have hplus :
            Tendsto (fun n : ℕ =>
                Finset.sum (Finset.range (n + 1)) (fun i => (1 : ℝ) / ((i : ℝ) + 1))) atTop atTop :=
          hharm.comp (tendsto_add_atTop_nat 1)
        have hEq :
            (fun n : ℕ =>
                Finset.sum (Finset.range (n + 1)) (fun i => (1 : ℝ) / ((i : ℝ) + 1)))
              = (fun n : ℕ =>
                  Finset.sum (Finset.range n) (fun i => (1 : ℝ) / ((i : ℝ) + 2)) + 1) := by
          funext n
          calc
            Finset.sum (Finset.range (n + 1)) (fun i => (1 : ℝ) / ((i : ℝ) + 1))
                = Finset.sum (Finset.range n)
                    (fun i => (1 : ℝ) / ((((i + 1 : ℕ) : ℝ) + 1))) + (1 : ℝ) := by
                    simpa using (Finset.sum_range_succ' (f := fun i => (1 : ℝ) / ((i : ℝ) + 1)) n)
            _ = Finset.sum (Finset.range n) (fun i => (1 : ℝ) / ((i : ℝ) + 2)) + 1 := by
                    congr 1
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
        have hplus' :
            Tendsto
              (fun n : ℕ => Finset.sum (Finset.range n) (fun i => (1 : ℝ) / ((i : ℝ) + 2)) + 1)
              atTop atTop := by
          exact hplus.congr' (Filter.EventuallyEq.of_eq hEq)
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
          (tendsto_atTop_add_const_right atTop (-1 : ℝ) hplus')
      have hscaled :
          Tendsto (fun n : ℕ =>
              (2 / Real.pi) * (Finset.sum (Finset.range n) (fun i => (1 : ℝ) / ((i : ℝ) + 2)))
            ) atTop atTop := by
        have hpos : 0 < (2 / Real.pi : ℝ) := by positivity
        exact (Filter.tendsto_const_mul_atTop_of_pos hpos).2 hshift_harm
      have hterm :
          (fun n : ℕ =>
              Finset.sum (Finset.range n)
                (fun i => (2 : ℝ) / (Real.pi + (Real.pi + Real.pi * (i : ℝ)))))
            =
            (fun n : ℕ =>
              (2 / Real.pi) * (Finset.sum (Finset.range n) (fun i => (1 : ℝ) / ((i : ℝ) + 2)))) := by
        funext n
        calc
          Finset.sum (Finset.range n)
              (fun i => (2 : ℝ) / (Real.pi + (Real.pi + Real.pi * (i : ℝ))))
              = Finset.sum (Finset.range n)
                  (fun i => (2 / Real.pi) * ((1 : ℝ) / ((i : ℝ) + 2))) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                field_simp [Real.pi_ne_zero]
                ring
          _ = (2 / Real.pi) * (Finset.sum (Finset.range n) (fun i => (1 : ℝ) / ((i : ℝ) + 2))) := by
                simp [Finset.mul_sum]
      have hlower_tendsto :
          Tendsto (fun n : ℕ =>
              Finset.sum (Finset.range n)
                (fun i => (2 : ℝ) / (Real.pi + (Real.pi + Real.pi * (i : ℝ)))))
            atTop atTop := by
        exact hscaled.congr' (Filter.EventuallyEq.of_eq hterm.symm)
      exact Filter.tendsto_atTop_mono hseq_lower hlower_tendsto
    exact not_tendsto_nhds_of_tendsto_atTop hseq_atTop l hseq_to_l

/-- Proposition 5.5.13 (integral test for series). If `f : [k, ∞) → ℝ` is
nonnegative and decreasing for some integer `k`, then the series
`∑_{n = k}^{∞} f n` converges if and only if the improper integral `∫ k^∞ f`
converges. In the convergent case,
`∫ k^∞ f ≤ ∑_{n = k}^{∞} f n ≤ f k + ∫ k^∞ f`. -/
theorem integral_test_for_series {f : ℝ → ℝ} {k : ℕ}
    (hmono : AntitoneOn f (Set.Ici (k : ℝ)))
    (hpos : ∀ x, (k : ℝ) ≤ x → 0 ≤ f x)
    (hInt : ∀ c, MeasureTheory.IntegrableOn f (Set.Icc (k : ℝ) c)) :
    (Summable (fun n : ℕ => f (n + k)) ↔ ImproperIntegralAtTopConverges f k) ∧
      (∀ {l}, ImproperIntegralAtTop f k l →
        Summable (fun n : ℕ => f (n + k)) →
          l ≤ tsum (fun n : ℕ => f (n + k)) ∧
            tsum (fun n : ℕ => f (n + k)) ≤ f k + l) := by
  let seq : ℕ → ℝ := fun n => f ((k : ℝ) + n)
  let S : ℕ → ℝ := fun n => Finset.sum (Finset.range n) seq
  let A : ℕ → ℝ := fun n => (∫ x in (k : ℝ)..((k : ℝ) + n), f x)

  have hseq_eq : (fun n : ℕ => f (n + k)) = seq := by
    funext n
    simp [seq, add_comm]

  have hseq_nonneg : ∀ n, 0 ≤ seq n := by
    intro n
    have hk : (k : ℝ) ≤ (k : ℝ) + n := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      linarith
    simpa [seq] using hpos ((k : ℝ) + n) hk

  have hA_mono : Monotone A := by
    intro m n hmn
    have hkm : (k : ℝ) ≤ (k : ℝ) + m := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
      linarith
    have hmn' : (k : ℝ) + m ≤ (k : ℝ) + n := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_left (Nat.cast_le.mpr hmn) (k : ℝ))
    exact intervalIntegral_mono_upper (f := f) (a := (k : ℝ))
      (hInt := hInt) (hpos := hpos) hkm hmn'

  have hmono_Icc : ∀ n : ℕ, AntitoneOn f (Set.Icc (k : ℝ) ((k : ℝ) + n)) := by
    intro n
    exact hmono.mono (by
      intro x hx
      exact hx.1)

  have hA_le_S : ∀ n, A n ≤ S n := by
    intro n
    simpa [A, S, seq, add_assoc, add_left_comm, add_comm] using
      (AntitoneOn.integral_le_sum (f := f) (x₀ := (k : ℝ)) (a := n) (hf := hmono_Icc n))

  have hshift_le_A : ∀ n, Finset.sum (Finset.range n) (fun i => seq (i + 1)) ≤ A n := by
    intro n
    simpa [A, seq, add_assoc, add_left_comm, add_comm] using
      (AntitoneOn.sum_le_integral (f := f) (x₀ := (k : ℝ)) (a := n) (hf := hmono_Icc n))

  have hS_le_fk_add_A : ∀ n, S n ≤ seq 0 + A n := by
    intro n
    cases n with
    | zero =>
        have h0 : 0 ≤ seq 0 := hseq_nonneg 0
        simpa [S, A] using h0
    | succ n =>
        have hA_step : A n ≤ A (n + 1) := hA_mono (Nat.le_succ n)
        calc
          S (n + 1) = seq 0 + Finset.sum (Finset.range n) (fun i => seq (i + 1)) := by
            calc
              S (n + 1) = Finset.sum (Finset.range (n + 1)) seq := by simp [S]
              _ = Finset.sum (Finset.range n) (fun i => seq (i + 1)) + seq 0 := by
                simpa using (Finset.sum_range_succ' (f := seq) n)
              _ = seq 0 + Finset.sum (Finset.range n) (fun i => seq (i + 1)) := by ring
          _ ≤ seq 0 + A n := by
            gcongr
            exact hshift_le_A n
          _ ≤ seq 0 + A (n + 1) := by
            gcongr

  have hS_step : ∀ n, S n ≤ S (n + 1) := by
    intro n
    calc
      S n ≤ S n + seq n := by
        linarith [hseq_nonneg n]
      _ = S (n + 1) := by
        simp [S, Finset.sum_range_succ, add_comm]

  have hS_mono : Monotone S := monotone_nat_of_le_succ hS_step

  have hsum_le_tsum : ∀ {hs : Summable seq} n, S n ≤ tsum seq := by
    intro hs n
    refine Summable.sum_le_tsum (s := Finset.range n) ?_ hs
    intro i hi
    exact hseq_nonneg i

  refine ⟨?_, ?_⟩
  · constructor
    · intro hs0
      have hs : Summable seq := by
        simpa [hseq_eq] using hs0
      let g : ℝ → ℝ := fun t => ∫ x in (k : ℝ)..max t (k : ℝ), f x
      let T : ℝ := tsum seq
      have hg_mono : Monotone g :=
        monotone_integral_max (f := f) (a := (k : ℝ)) hInt hpos
      have hg_le : ∀ t, g t ≤ T := by
        intro t
        let n : ℕ := Nat.ceil (max t (k : ℝ) - k)
        have hmaxk : (k : ℝ) ≤ max t (k : ℝ) := le_max_right t (k : ℝ)
        have hmaxn : max t (k : ℝ) ≤ (k : ℝ) + n := by
          have hceil : max t (k : ℝ) - k ≤ (n : ℝ) := Nat.le_ceil (max t (k : ℝ) - k)
          linarith
        have h1 :
            g t ≤ ∫ x in (k : ℝ)..((k : ℝ) + n), f x := by
          simpa [g] using
            (intervalIntegral_mono_upper (f := f) (a := (k : ℝ))
              (hInt := hInt) (hpos := hpos) (s := max t (k : ℝ)) (t := (k : ℝ) + n)
              hmaxk hmaxn)
        have h2 : ∫ x in (k : ℝ)..((k : ℝ) + n), f x ≤ S n := hA_le_S n
        exact h1.trans (h2.trans (hsum_le_tsum (hs := hs) n))
      have hgbdd : BddAbove (Set.range g) := by
        refine ⟨T, ?_⟩
        intro y hy
        rcases hy with ⟨t, rfl⟩
        exact hg_le t
      have hg_tend : Tendsto g atTop (nhds (⨆ t : ℝ, g t)) :=
        tendsto_atTop_ciSup hg_mono hgbdd
      have hEq :
          (fun c : ℝ => ∫ x in (k : ℝ)..c, f x) =ᶠ[atTop] g := by
        refine eventuallyEq_of_mem (Ioi_mem_atTop (k : ℝ)) ?_
        intro c hc
        have hck : (k : ℝ) ≤ c := le_of_lt hc
        simp [g, max_eq_left hck]
      have hTend :
          Tendsto (fun c : ℝ => ∫ x in (k : ℝ)..c, f x) atTop (nhds (⨆ t : ℝ, g t)) :=
        hg_tend.congr' hEq.symm
      exact ⟨⨆ t : ℝ, g t, ⟨hInt, hTend⟩⟩
    · intro hconv
      rcases hconv with ⟨l, hl⟩
      have hNat :
          Tendsto (fun n : ℕ => (k : ℝ) + n) atTop atTop := by
        have hNatCast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop
        simpa [add_assoc, add_left_comm, add_comm] using
          (Filter.tendsto_atTop_add_const_left (l := atTop) (C := (k : ℝ)) hNatCast)
      have hA_tend : Tendsto A atTop (nhds l) := by
        simpa [A] using (hl.2.comp hNat)
      have hA_event : ∀ᶠ n : ℕ in atTop, A n ≤ l + 1 := by
        refine (hA_tend.eventually (gt_mem_nhds (lt_add_of_pos_right l zero_lt_one))).mono ?_
        intro n hn
        exact hn.le
      rcases (Filter.eventually_atTop.mp hA_event) with ⟨N, hN⟩
      let c : ℝ := max (S N) (seq 0 + (l + 1))
      have hbound_sum : ∀ n, S n ≤ c := by
        intro n
        by_cases hn : n ≤ N
        · exact (hS_mono hn).trans (le_max_left _ _)
        · have hNn : N ≤ n := Nat.le_of_lt (lt_of_not_ge hn)
          have hA_n : A n ≤ l + 1 := hN n hNn
          have hS_n : S n ≤ seq 0 + A n := hS_le_fk_add_A n
          have hS_n' : S n ≤ seq 0 + (l + 1) := by
            exact hS_n.trans (by gcongr)
          exact hS_n'.trans (le_max_right _ _)
      have hs : Summable seq := by
        refine summable_of_sum_range_le (f := seq) (c := c) hseq_nonneg ?_
        intro n
        simpa [S, c] using hbound_sum n
      simpa [hseq_eq] using hs
  · intro l hl hs0
    have hs : Summable seq := by
      simpa [hseq_eq] using hs0
    let T : ℝ := tsum seq
    have hNat : Tendsto (fun n : ℕ => (k : ℝ) + n) atTop atTop := by
      have hNatCast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop
      simpa [add_assoc, add_left_comm, add_comm] using
        (Filter.tendsto_atTop_add_const_left (l := atTop) (C := (k : ℝ)) hNatCast)
    have hA_tend : Tendsto A atTop (nhds l) := by
      simpa [A] using (hl.2.comp hNat)
    have hS_tend : Tendsto S atTop (nhds T) := by
      simpa [S, T] using hs.hasSum.tendsto_sum_nat
    have hleft : l ≤ T := by
      refine tendsto_le_of_eventuallyLE hA_tend hS_tend ?_
      exact Filter.Eventually.of_forall hA_le_S
    have hright : T ≤ seq 0 + l := by
      have hSeqA_tend : Tendsto (fun n : ℕ => seq 0 + A n) atTop (nhds (seq 0 + l)) :=
        tendsto_const_nhds.add hA_tend
      refine tendsto_le_of_eventuallyLE hS_tend hSeqA_tend ?_
      exact Filter.Eventually.of_forall hS_le_fk_add_A
    refine ⟨?_, ?_⟩
    · simpa [T, hseq_eq] using hleft
    · simpa [T, seq, hseq_eq, add_assoc, add_left_comm, add_comm] using hright

/-- Telescoping sum for successive differences. -/
lemma sum_range_sub_telescope (u : ℕ → ℝ) :
    ∀ N, (Finset.sum (Finset.range N) fun n => u n - u (n + 1)) = u 0 - u N := by
  intro N
  induction N with
  | zero =>
      simp
  | succ N ih =>
      calc
        Finset.sum (Finset.range N.succ) (fun n => u n - u (n + 1))
            = Finset.sum (Finset.range N) (fun n => u n - u (n + 1)) +
                (u N - u (N + 1)) := by
              simpa using
                (Finset.sum_range_succ (f := fun n => u n - u (n + 1)) N)
        _ = (u 0 - u N) + (u N - u (N + 1)) := by simp [ih]
        _ = u 0 - u (N + 1) := by ring

/-- For `m ≥ 1`, the term `1 / m^2` dominates the telescoping difference
`1 / m - 1 / (m + 1)`. -/
lemma inv_sq_ge_sub_inv_succ {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) / (m : ℝ) ^ 2 ≥ 1 / (m : ℝ) - 1 / (m.succ : ℝ) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hm)
  have hm0' : (m : ℝ) ≠ 0 := ne_of_gt hm0
  have hdiff :
      1 / (m : ℝ) - 1 / (m.succ : ℝ) =
        1 / ((m : ℝ) * (m.succ : ℝ)) := by
    have hmsucc : (m.succ : ℝ) = (m : ℝ) + 1 := by norm_cast
    have hcalc :
        1 / (m : ℝ) - 1 / ((m : ℝ) + 1) =
          1 / ((m : ℝ) * ((m : ℝ) + 1)) := by
      have hpos : (m : ℝ) + 1 ≠ 0 := by nlinarith
      field_simp [hm0', hpos]
      ring_nf
    simpa [hmsucc] using hcalc
  have hmul_le : (m : ℝ) ^ 2 ≤ (m : ℝ) * (m.succ : ℝ) := by
    have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have hm_le : (m : ℝ) ≤ m.succ := by exact_mod_cast (Nat.le_succ m)
    nlinarith
  have hpos : 0 < (m : ℝ) ^ 2 := pow_pos hm0 _
  have hrecip :
      1 / ((m : ℝ) * (m.succ : ℝ)) ≤ 1 / (m : ℝ) ^ 2 :=
    one_div_le_one_div_of_le hpos hmul_le
  calc
    1 / (m : ℝ) - 1 / (m.succ : ℝ)
        = 1 / ((m : ℝ) * (m.succ : ℝ)) := hdiff
    _ ≤ 1 / (m : ℝ) ^ 2 := hrecip

/-- For `m ≥ 1`, the next term `1 / (m + 1)^2` is bounded above by the same
telescoping difference `1 / m - 1 / (m + 1)`. -/
lemma inv_sq_succ_le_sub_inv {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) / (m.succ : ℝ) ^ 2 ≤ 1 / (m : ℝ) - 1 / (m.succ : ℝ) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hm)
  have hm0' : (m : ℝ) ≠ 0 := ne_of_gt hm0
  have hmpos_succ : 0 < (m.succ : ℝ) := by exact_mod_cast (Nat.succ_pos m)
  have hdiff :
      1 / (m : ℝ) - 1 / (m.succ : ℝ) =
        1 / ((m : ℝ) * (m.succ : ℝ)) := by
    have hmsucc : (m.succ : ℝ) = (m : ℝ) + 1 := by norm_cast
    have hcalc :
        1 / (m : ℝ) - 1 / ((m : ℝ) + 1) =
          1 / ((m : ℝ) * ((m : ℝ) + 1)) := by
      have hpos : (m : ℝ) + 1 ≠ 0 := by nlinarith
      field_simp [hm0', hpos]
      ring_nf
    simpa [hmsucc] using hcalc
  have hmul_le : (m : ℝ) * (m.succ : ℝ) ≤ (m.succ : ℝ) ^ 2 := by
    have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have hm_le : (m : ℝ) ≤ m.succ := by exact_mod_cast (Nat.le_succ m)
    nlinarith
  have hpos : 0 < (m : ℝ) * (m.succ : ℝ) := by
    nlinarith [hm0, hmpos_succ]
  have hrecip :
      1 / (m.succ : ℝ) ^ 2 ≤ 1 / ((m : ℝ) * (m.succ : ℝ)) :=
    one_div_le_one_div_of_le hpos hmul_le
  calc
    (1 : ℝ) / (m.succ : ℝ) ^ 2
        ≤ 1 / ((m : ℝ) * (m.succ : ℝ)) := hrecip
    _ = 1 / (m : ℝ) - 1 / (m.succ : ℝ) := hdiff.symm

set_option maxHeartbeats 10000000 in
-- The following summation estimate needs extra heartbeats.
lemma tail_bounds_one_div_nat_sq {k : ℕ} (hk : 1 ≤ k) :
    1 / (k : ℝ) ≤ tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) ∧
      tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) ≤
        1 / (k : ℝ) ^ 2 + 1 / (k : ℝ) := by
  classical
  have hbase :
      Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) :=
    (Real.summable_one_div_nat_pow).2 (by decide)
  have hs :
      Summable (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).2 hbase
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have htail_sum :
      Summable (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff k).2 hbase
  let u : ℕ → ℝ := fun n => (1 : ℝ) / ((n + k : ℕ) : ℝ)
  let g : ℕ → ℝ := fun n => u n - u (n + 1)
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    have hkpos : 0 < k := Nat.succ_le_iff.mp hk
    have hpos_nat : 0 < n + k := Nat.add_pos_right n hkpos
    have hpos : 0 < (n + k : ℝ) := by exact_mod_cast hpos_nat
    have hle : u (n + 1) ≤ u n := by
      have hle' : (n + k : ℝ) ≤ (n + k + 1 : ℝ) := by nlinarith
      have := one_div_le_one_div_of_le hpos hle'
      simpa [u, Nat.cast_add, Nat.cast_one, add_assoc, add_comm] using this
    exact sub_nonneg.mpr hle
  have hu : Tendsto u atTop (nhds 0) := by
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa [u, Nat.cast_add, Nat.cast_one] using
      ((tendsto_add_atTop_iff_nat k).2 h0)
  have hsum_g : HasSum g (1 / (k : ℝ)) := by
    have htel := sum_range_sub_telescope u
    have hlim :
        Tendsto (fun n => u 0 - u n) atTop (nhds ((u 0) - 0)) :=
      (tendsto_const_nhds.sub hu)
    have hpartial :
        Tendsto (fun n : ℕ => Finset.sum (Finset.range n) (fun i => g i))
          atTop (nhds (u 0)) := by
      simpa [g, htel] using hlim
    have hnonneg : ∀ i, 0 ≤ g i := hg_nonneg
    have hhas :=
      (hasSum_iff_tendsto_nat_of_nonneg hnonneg (u 0)).2 hpartial
    simpa [u, Nat.cast_add, Nat.cast_one] using hhas
  have tsum_g : tsum g = 1 / (k : ℝ) := hsum_g.tsum_eq
  have htail_lower :
      1 / (k : ℝ) ≤
        tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) := by
    have hle :
        ∀ n, g n ≤ (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) n := by
      intro n
      have hk'' : 1 ≤ n + k := by
        have h1 : 1 ≤ n + 1 := by exact Nat.succ_le_succ (Nat.zero_le n)
        exact le_trans h1 (Nat.add_le_add_left hk n)
      have := inv_sq_ge_sub_inv_succ (m := n + k) (by exact hk'')
      simpa [g, u, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    have := Summable.tsum_le_tsum (h := hle) hsum_g.summable htail_sum
    simpa [tsum_g] using this
  have htail_split :
      tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) =
        (1 : ℝ) / (k : ℝ) ^ 2 +
          tsum (fun n : ℕ => (1 : ℝ) / ((n + k.succ : ℕ) : ℝ) ^ 2) :=
    by
      have := htail_sum.tsum_eq_zero_add
      simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm,
        add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  have htail_succ_sum :
      Summable (fun n : ℕ => (1 : ℝ) / ((n + k.succ : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff k.succ).2 hbase
  have hupper_comp :
      ∀ n,
        (fun n : ℕ => (1 : ℝ) / ((n + k.succ : ℕ) : ℝ) ^ 2) n ≤ g n := by
    intro n
    have hk'' : 1 ≤ n + k := by
      have h1 : 1 ≤ n + 1 := by exact Nat.succ_le_succ (Nat.zero_le n)
      exact le_trans h1 (Nat.add_le_add_left hk n)
    have := inv_sq_succ_le_sub_inv (m := n + k) hk''
    simpa [g, u, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  have htail_succ_le : tsum (fun n : ℕ => (1 : ℝ) / ((n + k.succ : ℕ) : ℝ) ^ 2) ≤
      tsum g :=
    Summable.tsum_le_tsum (h := hupper_comp) htail_succ_sum hsum_g.summable
  have htail_upper :
      tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) ≤
        1 / (k : ℝ) ^ 2 + 1 / (k : ℝ) := by
    calc
      tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2)
          = (1 : ℝ) / (k : ℝ) ^ 2 +
              tsum (fun n : ℕ => (1 : ℝ) / ((n + k.succ : ℕ) : ℝ) ^ 2) :=
            htail_split
      _ ≤ (1 : ℝ) / (k : ℝ) ^ 2 + tsum g := by
            have := htail_succ_le
            linarith
      _ = 1 / (k : ℝ) ^ 2 + 1 / (k : ℝ) := by
            simp [tsum_g, add_comm]
  exact ⟨htail_lower, htail_upper⟩

/-- Example 5.5.14. Using the integral test with `f x = 1 / x^2` gives explicit
bounds on the Basel series. For any integer `k ≥ 1`,
`∑_{n=1}^{k-1} 1 / n^2 + 1 / k ≤ ∑_{n=1}^{∞} 1 / n^2 ≤
∑_{n=1}^{k-1} 1 / n^2 + 1 / k + 1 / k^2`. Numerically, taking `k = 10`
shows the sum lies between `1.6397…` and `1.6497…`, while the exact value is
`π^2 / 6 ≈ 1.6449…`. -/
theorem series_one_div_nat_sq_bounds {k : ℕ} (hk : 1 ≤ k) :
    Summable (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) ∧
      ((Finset.sum (Finset.range (k - 1))
            (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) + 1 / (k : ℝ) ≤
        tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2)) ∧
      (tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) ≤
        Finset.sum (Finset.range (k - 1))
    (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) + 1 / (k : ℝ) +
          1 / ((k : ℝ) ^ 2))) :=
by
  classical
  -- Basic summability of the p-series with `p = 2`.
  have hbase :
      Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) :=
    (Real.summable_one_div_nat_pow).2 (by decide)
  have hs :
      Summable (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).2 hbase
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  -- Splitting the full sum into the first `k - 1` terms and the tail.
  have hsplit :
      Finset.sum (Finset.range (k - 1))
            (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) +
          tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) =
        tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) := by
    simpa [hk', Nat.succ_eq_add_one, Nat.add_assoc] using
      (Summable.sum_add_tsum_nat_add (k := k - 1) hs)
  have htsum_comm :
      tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) +
        Finset.sum (Finset.range (k - 1))
          (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) =
      tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) := by
    calc
      tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) +
            Finset.sum (Finset.range (k - 1))
              (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2)
          =
          Finset.sum (Finset.range (k - 1))
              (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) +
            tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) := by
        ac_rfl
      _ = tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) := hsplit
  have htail := tail_bounds_one_div_nat_sq hk
  -- Assemble the bounds.
  constructor
  · exact hs
  constructor
  · -- Lower bound with the partial sum.
    have hineq :=
      add_le_add_left htail.1
        (Finset.sum (Finset.range (k - 1))
          (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2))
    have hsum_le :
        Finset.sum (Finset.range (k - 1))
              (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) + 1 / (k : ℝ) ≤
          tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) := by
      have hrewrite := hsplit
      linarith
    exact hsum_le
  · -- Upper bound with the partial sum.
    have htsum :
        tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) =
          Finset.sum (Finset.range (k - 1))
              (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) +
            tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) := by
      exact hsplit.symm
    have hbound :
        tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) ≤
          Finset.sum (Finset.range (k - 1))
              (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) +
            (1 / (k : ℝ) ^ 2 + 1 / (k : ℝ)) := by
      calc
        tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2)
            = Finset.sum (Finset.range (k - 1))
                  (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) +
                tsum (fun n : ℕ => (1 : ℝ) / ((n + k : ℕ) : ℝ) ^ 2) := htsum
        _ ≤ Finset.sum (Finset.range (k - 1))
                (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) +
              (1 / (k : ℝ) ^ 2 + 1 / (k : ℝ)) := by
              linarith [htail.2]
    calc
      tsum (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) ≤
          Finset.sum (Finset.range (k - 1))
              (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) +
            (1 / (k : ℝ) ^ 2 + 1 / (k : ℝ)) := hbound
      _ =
          Finset.sum (Finset.range (k - 1))
              (fun n : ℕ => (1 : ℝ) / (n.succ : ℝ) ^ 2) +
            1 / (k : ℝ) + 1 / (k : ℝ) ^ 2 := by
        ac_rfl

end Section05
end Chap05
