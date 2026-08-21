/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Shu Miao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section08_part5

noncomputable section
open scoped RealInnerProductSpace
open scoped Pointwise Topology
open Metric

section Chap02
section Section08

/-- Each recession difference is bounded above by `f0_plus`. -/
lemma recessionFunction_diff_le_sup {n : Nat}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal |
            ∃ x ∈ (Set.univ : Set (Fin n → Real)),
              r = ((f (x + y) - f x : Real) : EReal) }) :
    ∀ x y : Fin n → Real, ((f (x + y) - f x : Real) : EReal) ≤ f0_plus y := by
  intro x y
  have hmem :
      ((f (x + y) - f x : Real) : EReal) ∈
        { r : EReal |
          ∃ x ∈ (Set.univ : Set (Fin n → Real)),
            r = ((f (x + y) - f x : Real) : EReal) } := by
    exact ⟨x, by simp, rfl⟩
  have hle :
      ((f (x + y) - f x : Real) : EReal) ≤
        sSup { r : EReal |
          ∃ x ∈ (Set.univ : Set (Fin n → Real)),
            r = ((f (x + y) - f x : Real) : EReal) } :=
    le_sSup hmem
  simpa [hf0_plus y] using hle

/-- The recession function controls increments of `f`. -/
lemma recessionFunction_additive_majorant {n : Nat}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal |
            ∃ x ∈ (Set.univ : Set (Fin n → Real)),
              r = ((f (x + y) - f x : Real) : EReal) }) :
    ∀ x y : Fin n → Real, (f (x + y) : EReal) ≤ (f x : EReal) + f0_plus y := by
  intro x y
  have hdiff :
      ((f (x + y) - f x : Real) : EReal) ≤ f0_plus y :=
    recessionFunction_diff_le_sup (f := f) (f0_plus := f0_plus) hf0_plus x y
  have hsum_le :
      (f x : EReal) + ((f (x + y) - f x : Real) : EReal) ≤ (f x : EReal) + f0_plus y := by
    exact add_le_add_right hdiff (f x : EReal)
  have hsum :
      (f x : EReal) + ((f (x + y) - f x : Real) : EReal) = (f (x + y) : EReal) := by
    have hsum' : f x + (f (x + y) - f x) = f (x + y) := by
      linarith
    calc
      (f x : EReal) + ((f (x + y) - f x : Real) : EReal) =
          ((f x + (f (x + y) - f x) : Real) : EReal) := by
            simpa using (EReal.coe_add (f x) (f (x + y) - f x)).symm
      _ = (f (x + y) : EReal) := by
          simp [hsum']
  calc
    (f (x + y) : EReal) =
        (f x : EReal) + ((f (x + y) - f x : Real) : EReal) := by
          symm
          exact hsum
    _ ≤ (f x : EReal) + f0_plus y := hsum_le

/-- Any additive majorant bounds the recession function pointwise. -/
lemma recessionFunction_le_of_additive_majorant {n : Nat}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal |
            ∃ x ∈ (Set.univ : Set (Fin n → Real)),
              r = ((f (x + y) - f x : Real) : EReal) })
    (hne : ∀ x : Fin n → Real, (f x : EReal) ≠ (⊥ : EReal)) :
    ∀ h : (Fin n → Real) → EReal,
      (∀ z x : Fin n → Real, (f z : EReal) ≤ (f x : EReal) + h (z - x)) →
        f0_plus ≤ h := by
  classical
  intro h hmajor y
  have hf0_plus_eq :
      f0_plus y =
        ⨆ x : Fin n → Real, ((f (x + y) - f x : Real) : EReal) :=
    recessionFunction_iSup_formula (C := Set.univ) (f := f) (f0_plus := f0_plus) (hC := rfl)
      hf0_plus y
  have hsup :
      (⨆ x : Fin n → Real, ((f (x + y) - f x : Real) : EReal)) ≤ h y := by
    refine iSup_le ?_
    intro x
    have hxy : (f (x + y) : EReal) ≤ (f x : EReal) + h y := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmajor (x + y) x
    rcases (EReal.exists (p := fun r => r = h y)).1 ⟨h y, rfl⟩ with hy_bot | hy_top | hy_real
    · have hy_bot' : h y = (⊥ : EReal) := hy_bot.symm
      have hxy' : (f (x + y) : EReal) ≤ (⊥ : EReal) := by
        have hxy'' := hxy
        simp [hy_bot'] at hxy''
      have hbot : (f (x + y) : EReal) = (⊥ : EReal) := (le_bot_iff).1 hxy'
      exact (hne (x + y) hbot).elim
    · have hy_top' : h y = (⊤ : EReal) := hy_top.symm
      simp [hy_top']
    · rcases hy_real with ⟨v, hv⟩
      have hxy' : (f (x + y) : EReal) ≤ (f x : EReal) + (v : EReal) := by
        simpa [hv] using hxy
      have hxy_real : f (x + y) ≤ f x + v := by
        have hxy'' : (f (x + y) : EReal) ≤ ((f x + v : Real) : EReal) := by
          simpa [EReal.coe_add] using hxy'
        exact (EReal.coe_le_coe_iff).1 hxy''
      have hdiff_real : f (x + y) - f x ≤ v := by
        linarith
      have hdiff : ((f (x + y) - f x : Real) : EReal) ≤ (v : EReal) :=
        (EReal.coe_le_coe_iff).2 hdiff_real
      simpa [hv] using hdiff
  simpa [hf0_plus_eq] using hsup

/-- Corollary 8.5.1. Let `f` be a proper convex function. Then `f0^+` is the least of the
functions `h` such that `f(z) ≤ f(x) + h(z - x)` for all `z` and all `x`. The recession
function of `f` can be viewed in terms of a closure construction when `f` is a closed proper
convex function; the source text continues with "Let g be the positively ..." (truncated). -/
theorem recessionFunction_least_additive_majorant {n : Nat}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)))
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal |
            ∃ x ∈ (Set.univ : Set (Fin n → Real)),
              r = ((f (x + y) - f x : Real) : EReal) }) :
    (∀ z x : Fin n → Real, (f z : EReal) ≤ (f x : EReal) + f0_plus (z - x)) ∧
      (∀ h : (Fin n → Real) → EReal,
        (∀ z x : Fin n → Real, (f z : EReal) ≤ (f x : EReal) + h (z - x)) →
          f0_plus ≤ h) := by
  refine ⟨?_, ?_⟩
  · intro z x
    have hxy :
        (f (x + (z - x)) : EReal) ≤ (f x : EReal) + f0_plus (z - x) :=
      recessionFunction_additive_majorant (f := f) (f0_plus := f0_plus) hf0_plus x (z - x)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxy
  · intro h hmajor
    have hne : ∀ x : Fin n → Real, (f x : EReal) ≠ (⊥ : EReal) := by
      intro x
      exact hf.2.2 x (by simp)
    exact
      recessionFunction_le_of_additive_majorant (f := f) (f0_plus := f0_plus) hf0_plus hne h
        hmajor

/-- Convert a right-sided limit at `0` into a limit at `+∞` via inversion. -/
lemma tendsto_rightScalarMultiple_comp_inv {n : Nat} {f : (Fin n → Real) → EReal}
    {y : Fin n → Real} {l : Filter EReal} :
    Filter.Tendsto (fun t : ℝ => rightScalarMultiple f t y) (𝓝[>] (0 : ℝ)) l ↔
      Filter.Tendsto (fun t : ℝ => rightScalarMultiple f (t⁻¹) y) Filter.atTop l := by
  constructor
  · intro h
    exact h.comp tendsto_inv_atTop_nhdsGT_zero
  · intro h
    have h' :
        Filter.Tendsto (fun t : ℝ => rightScalarMultiple f ((t⁻¹)⁻¹) y) (𝓝[>] (0 : ℝ)) l :=
      h.comp tendsto_inv_nhdsGT_zero
    simpa using h'

/-- Positive right scalar multiples satisfy the usual scaling formula. -/
lemma rightScalarMultiple_pos_rewrite {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunction f) {lam : Real} (hlam : 0 < lam) (x : Fin n → Real) :
    rightScalarMultiple f lam x = ((lam : Real) : EReal) * f (lam⁻¹ • x) := by
  have hf' : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
    simpa [ConvexFunction] using hf
  simpa using rightScalarMultiple_pos (f := f) (lam := lam) hf' hlam x

/-- A ray difference-quotient limit yields the inverse right scalar multiple limit. -/
lemma tendsto_rightScalarMultiple_inv_of_ray_limit {n : Nat}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal} {y : Fin n → Real}
    (hfconv : ConvexFunction (fun x => (f x : EReal)))
    (hlim :
      Filter.Tendsto
        (fun t : Real => (((f (t • y) - f 0) / t : Real) : EReal))
        Filter.atTop (𝓝 (f0_plus y))) :
    Filter.Tendsto
      (fun t : Real => rightScalarMultiple (fun x => (f x : EReal)) (t⁻¹) y)
      Filter.atTop (𝓝 (f0_plus y)) := by
  have hpos : ∀ᶠ t : ℝ in Filter.atTop, 0 < t := by
    refine (Filter.eventually_atTop.2 ?_)
    refine ⟨1, ?_⟩
    intro t ht
    linarith
  have hrewrite :
      (fun t : Real => rightScalarMultiple (fun x => (f x : EReal)) (t⁻¹) y) =ᶠ[Filter.atTop]
        fun t => ((t⁻¹ : Real) : EReal) * (f (t • y) : EReal) := by
    refine hpos.mono ?_
    intro t ht
    have ht' : 0 < (t⁻¹ : Real) := inv_pos.mpr ht
    simpa using
      (rightScalarMultiple_pos_rewrite (f := fun x => (f x : EReal)) (hf := hfconv)
        (lam := t⁻¹) (hlam := ht') (x := y))
  have hconst_real :
      Filter.Tendsto (fun t : Real => f 0 / t) Filter.atTop (𝓝 (0 : Real)) := by
    have hmul :
        Filter.Tendsto (fun t : Real => (f 0) * t⁻¹) Filter.atTop (𝓝 ((f 0) * 0)) :=
      (tendsto_inv_atTop_zero.const_mul (f 0))
    simpa [div_eq_mul_inv] using hmul
  have hconst :
      Filter.Tendsto (fun t : Real => ((f 0 / t : Real) : EReal)) Filter.atTop (𝓝 (0 : EReal)) := by
    simpa using (EReal.tendsto_coe.2 hconst_real)
  have hsum :
      Filter.Tendsto
        (fun t : Real =>
          (((f (t • y) - f 0) / t : Real) : EReal) + ((f 0 / t : Real) : EReal))
        Filter.atTop (𝓝 (f0_plus y)) := by
    have hpair :
        Filter.Tendsto
          (fun t : Real =>
            ( (((f (t • y) - f 0) / t : Real) : EReal), ((f 0 / t : Real) : EReal) ))
          Filter.atTop (𝓝 (f0_plus y, (0 : EReal))) :=
      hlim.prodMk_nhds hconst
    have hadd :
        Filter.Tendsto (fun p : EReal × EReal => p.1 + p.2)
          (𝓝 (f0_plus y, (0 : EReal))) (𝓝 (f0_plus y + (0 : EReal))) :=
      (EReal.continuousAt_add (p := (f0_plus y, (0 : EReal))) (Or.inr (by simp))
        (Or.inr (by simp))).tendsto
    have hsum' := hadd.comp hpair
    simpa using hsum'
  have hrewrite2 :
      (fun t : Real => ((t⁻¹ : Real) : EReal) * (f (t • y) : EReal)) =ᶠ[Filter.atTop]
        fun t =>
          (((f (t • y) - f 0) / t : Real) : EReal) + ((f 0 / t : Real) : EReal) := by
    refine (Filter.eventually_atTop.2 ?_)
    refine ⟨0, ?_⟩
    intro t _
    have hreal :
        t⁻¹ * f (t • y) =
          ((f (t • y) - f 0) / t) + (f 0 / t) := by
      calc
        t⁻¹ * f (t • y) = (f (t • y)) * t⁻¹ := by ring
        _ = (f (t • y) - f 0 + f 0) * t⁻¹ := by ring
        _ = (f (t • y) - f 0) * t⁻¹ + f 0 * t⁻¹ := by ring
        _ = ((f (t • y) - f 0) / t) + (f 0 / t) := by
              simp [div_eq_mul_inv, mul_comm]
    have hreal' :
        ((t⁻¹ * f (t • y) : Real) : EReal) =
          (((f (t • y) - f 0) / t + f 0 / t : Real) : EReal) :=
      congrArg (fun r : Real => (r : EReal)) hreal
    calc
      ((t⁻¹ : Real) : EReal) * (f (t • y) : EReal)
          = ((t⁻¹ * f (t • y) : Real) : EReal) := by
              simp [EReal.coe_mul]
      _ = (((f (t • y) - f 0) / t + f 0 / t : Real) : EReal) := hreal'
      _ =
          (((f (t • y) - f 0) / t : Real) : EReal) + ((f 0 / t : Real) : EReal) := by
            simp [EReal.coe_add]
  have hsum' :
      Filter.Tendsto
        (fun t : Real => ((t⁻¹ : Real) : EReal) * (f (t • y) : EReal))
        Filter.atTop (𝓝 (f0_plus y)) :=
    Filter.Tendsto.congr' hrewrite2.symm hsum
  exact Filter.Tendsto.congr' hrewrite.symm hsum'

/-- Corollary 8.5.2. If `f` is a closed proper convex function, then
`(f0^+)(y) = lim_{λ ↑ 0} (f λ)(y)` for every `y ∈ dom f`. If `0 ∈ dom f`, this
formula holds for every `y ∈ ℝ^n`. -/
theorem recessionFunction_limit_rightScalarMultiple {n : Nat}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hfclosed : ClosedConvexFunction (fun x => (f x : EReal)))
    (hfproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)))
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal |
            ∃ x ∈ (Set.univ : Set (Fin n → Real)),
              r = ((f (x + y) - f x : Real) : EReal) }) :
    (∀ y ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)),
        Filter.Tendsto
          (fun t : ℝ => rightScalarMultiple (fun x => (f x : EReal)) t y)
          (𝓝[>] (0 : ℝ)) (𝓝 (f0_plus y))) ∧
      ((0 : Fin n → Real) ∈
          effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)) →
        ∀ y : Fin n → Real,
          Filter.Tendsto
            (fun t : ℝ => rightScalarMultiple (fun x => (f x : EReal)) t y)
            (𝓝[>] (0 : ℝ)) (𝓝 (f0_plus y))) := by
  have hprop :=
    recessionFunction_properties (C := Set.univ) (f := f) (f0_plus := f0_plus)
      hfproper rfl hf0_plus
  have hconv : ConvexFunction (fun x => (f x : EReal)) := by
    simpa [ConvexFunction] using hfproper.1
  have hlim_ray :
      ∀ y : Fin n → Real,
        Filter.Tendsto
          (fun t : Real => (((f (t • y) - f 0) / t : Real) : EReal))
          Filter.atTop (𝓝 (f0_plus y)) := by
    have hclosed := hprop.2.2.2 hfclosed
    intro y
    simpa using (hclosed.2 0 (by simp) y).2
  have hlim_inv :
      ∀ y : Fin n → Real,
        Filter.Tendsto
          (fun t : Real => rightScalarMultiple (fun x => (f x : EReal)) (t⁻¹) y)
          Filter.atTop (𝓝 (f0_plus y)) := by
    intro y
    exact
      tendsto_rightScalarMultiple_inv_of_ray_limit (f := f) (f0_plus := f0_plus) (y := y) hconv
        (hlim_ray y)
  refine ⟨?hdom, ?hall⟩
  · intro y hy
    have hchange :
        Filter.Tendsto
            (fun t : ℝ => rightScalarMultiple (fun x => (f x : EReal)) t y) (𝓝[>] (0 : ℝ))
            (𝓝 (f0_plus y)) ↔
          Filter.Tendsto
            (fun t : ℝ => rightScalarMultiple (fun x => (f x : EReal)) (t⁻¹) y)
            Filter.atTop
            (𝓝 (f0_plus y)) :=
      tendsto_rightScalarMultiple_comp_inv (f := fun x => (f x : EReal)) (y := y)
        (l := 𝓝 (f0_plus y))
    exact hchange.2 (hlim_inv y)
  · intro h0 y
    have hchange :
        Filter.Tendsto
            (fun t : ℝ => rightScalarMultiple (fun x => (f x : EReal)) t y) (𝓝[>] (0 : ℝ))
            (𝓝 (f0_plus y)) ↔
          Filter.Tendsto
            (fun t : ℝ => rightScalarMultiple (fun x => (f x : EReal)) (t⁻¹) y)
            Filter.atTop
            (𝓝 (f0_plus y)) :=
      tendsto_rightScalarMultiple_comp_inv (f := fun x => (f x : EReal)) (y := y)
        (l := 𝓝 (f0_plus y))
    exact hchange.2 (hlim_inv y)

/-- Antitone along all base points is equivalent to nonpositive forward steps. -/
lemma ray_antitone_all_iff_nonpos_step {n : Nat} {f : (Fin n → Real) → EReal} {y : Fin n → Real} :
    (∀ x : Fin n → Real, Antitone (fun t : ℝ => f (x + t • y))) ↔
      ∀ x : Fin n → Real, ∀ t : ℝ, 0 ≤ t → f (x + t • y) ≤ f x := by
  constructor
  · intro h x t ht
    have hanti := h x
    have hle := hanti (a := 0) (b := t) ht
    simpa using hle
  · intro h x s t hst
    have ht : 0 ≤ t - s := sub_nonneg.mpr hst
    have hstep := h (x + s • y) (t - s) ht
    have hrew : x + t • y = x + s • y + (t - s) • y := by
      have hrew' : t • y = s • y + (t - s) • y := by
        have hscalar : s + (t - s) = t := by ring
        have h' : s • y + (t - s) • y = t • y := by
          calc
            s • y + (t - s) • y = (s + (t - s)) • y := by
              simpa using (add_smul s (t - s) y).symm
            _ = t • y := by simp [hscalar]
        simpa using h'.symm
      calc
        x + t • y = x + (s • y + (t - s) • y) := by simp [hrew']
        _ = x + s • y + (t - s) • y := by simp [add_assoc]
    simpa [hrew.symm, add_assoc] using hstep

/-- Antitone along all base points is equivalent to nonpositive forward steps (real-valued). -/
lemma ray_antitone_all_iff_nonpos_step_real {n : Nat} {f : (Fin n → Real) → Real}
    {y : Fin n → Real} :
    (∀ x : Fin n → Real, Antitone (fun t : ℝ => f (x + t • y))) ↔
      ∀ x : Fin n → Real, ∀ t : ℝ, 0 ≤ t → f (x + t • y) ≤ f x := by
  constructor
  · intro h x t ht
    have hanti := h x
    have hle := hanti (a := 0) (b := t) ht
    simpa using hle
  · intro h x s t hst
    have ht : 0 ≤ t - s := sub_nonneg.mpr hst
    have hstep := h (x + s • y) (t - s) ht
    have hrew : x + t • y = x + s • y + (t - s) • y := by
      have hrew' : t • y = s • y + (t - s) • y := by
        have hscalar : s + (t - s) = t := by ring
        have h' : s • y + (t - s) • y = t • y := by
          calc
            s • y + (t - s) • y = (s + (t - s)) • y := by
              simpa using (add_smul s (t - s) y).symm
            _ = t • y := by simp [hscalar]
        simpa using h'.symm
      calc
        x + t • y = x + (s • y + (t - s) • y) := by simp [hrew']
        _ = x + s • y + (t - s) • y := by simp [add_assoc]
    simpa [hrew.symm, add_assoc] using hstep

/-- Antitone along all base points is equivalent to nonpositive ray difference quotients. -/
lemma ray_antitone_all_iff_diffquotient_le_zero_real {n : Nat}
    {f : (Fin n → Real) → Real} {y : Fin n → Real} :
    (∀ x : Fin n → Real, Antitone (fun t : ℝ => f (x + t • y))) ↔
      ∀ x : Fin n → Real, ∀ t : ℝ, 0 < t →
        ((f (x + t • y) - f x) / t : Real) ≤ 0 := by
  constructor
  · intro h x t ht
    have hstep :
        f (x + t • y) ≤ f x :=
      (ray_antitone_all_iff_nonpos_step_real (f := f) (y := y)).1 h x t (le_of_lt ht)
    have hdiff : f (x + t • y) - f x ≤ 0 := by linarith
    have hquot : (f (x + t • y) - f x) / t ≤ (0 : Real) :=
      (div_le_iff₀ ht).2 (by simpa using hdiff)
    simpa using hquot
  · intro h
    have hstep : ∀ x : Fin n → Real, ∀ t : ℝ, 0 ≤ t → f (x + t • y) ≤ f x := by
      intro x t ht
      by_cases hpos : 0 < t
      · have hquot := h x t hpos
        have hdiff : f (x + t • y) - f x ≤ 0 := by
          have := (div_le_iff₀ hpos).1 hquot
          simpa using this
        linarith
      · have ht0 : t = 0 := le_antisymm (le_of_not_gt hpos) ht
        subst ht0
        simp
    exact (ray_antitone_all_iff_nonpos_step_real (f := f) (y := y)).2 hstep

/-- Finite liminf along a ray forces antitone behavior of the ray. -/
lemma ray_antitone_of_liminf_lt_top_real {n : Nat} {f : (Fin n → Real) → Real}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)))
    {x y : Fin n → Real} :
    Filter.liminf (fun t : ℝ => (f (x + t • y) : EReal)) Filter.atTop < (⊤ : EReal) →
      Antitone (fun t : ℝ => f (x + t • y)) := by
  classical
  intro hlim s t hst
  by_cases hst_eq : s = t
  · subst hst_eq
    exact le_rfl
  · have hst_lt : s < t := lt_of_le_of_ne hst hst_eq
    by_contra hle
    have hlt : f (x + s • y) < f (x + t • y) := lt_of_not_ge hle
    let v : ℝ := (f (x + t • y) - f (x + s • y)) / (t - s)
    have hvpos : 0 < v := by
      have hnum : 0 < f (x + t • y) - f (x + s • y) := sub_pos.mpr hlt
      have hden : 0 < t - s := sub_pos.mpr hst_lt
      exact div_pos hnum hden
    have hbound :
        ∀ M : ℝ, ∀ᶠ u : ℝ in Filter.atTop, (M : EReal) ≤ (f (x + u • y) : EReal) := by
      intro M
      refine (Filter.eventually_atTop).2 ?_
      refine ⟨max t (s + (M - f (x + s • y)) / v), ?_⟩
      intro u hu
      have hu_t : t ≤ u := le_of_max_le_left hu
      have hu_s : s + (M - f (x + s • y)) / v ≤ u := le_of_max_le_right hu
      have hus_pos : 0 < u - s := sub_pos.mpr (lt_of_lt_of_le hst_lt hu_t)
      have hmono :=
        differenceQuotient_monotone (C := Set.univ) (f := f) (hC := rfl) hf
          (x := x + s • y) (y := y)
      have hquot :
          (f (x + t • y) - f (x + s • y)) / (t - s) ≤
            (f (x + u • y) - f (x + s • y)) / (u - s) := by
        have hpos1 : 0 < t - s := sub_pos.mpr hst_lt
        have hpos2 : 0 < u - s := hus_pos
        have hle : (t - s : ℝ) ≤ u - s := sub_le_sub_right hu_t s
        have hmono' := hmono (a := ⟨t - s, hpos1⟩) (b := ⟨u - s, hpos2⟩) hle
        have hrew_t : x + s • y + (t - s) • y = x + t • y := by
          calc
            x + s • y + (t - s) • y = x + (s • y + (t - s) • y) := by
              simp [add_assoc]
            _ = x + (s + (t - s)) • y := by
              have hadd : s • y + (t - s) • y = (s + (t - s)) • y := by
                simpa using (add_smul s (t - s) y).symm
              simp [hadd]
            _ = x + t • y := by
              have hscalar : s + (t - s) = t := by ring
              simp [hscalar]
        have hrew_u : x + s • y + (u - s) • y = x + u • y := by
          calc
            x + s • y + (u - s) • y = x + (s • y + (u - s) • y) := by
              simp [add_assoc]
            _ = x + (s + (u - s)) • y := by
              have hadd : s • y + (u - s) • y = (s + (u - s)) • y := by
                simpa using (add_smul s (u - s) y).symm
              simp [hadd]
            _ = x + u • y := by
              have hscalar : s + (u - s) = u := by ring
              simp [hscalar]
        simpa [hrew_t, hrew_u, add_assoc] using hmono'
      have hquot' :
          v ≤ (f (x + u • y) - f (x + s • y)) / (u - s) := by
        simpa [v] using hquot
      have hdiff :
          v * (u - s) ≤ f (x + u • y) - f (x + s • y) := by
        exact (le_div_iff₀ hus_pos).1 hquot'
      have hlinear :
          f (x + u • y) ≥ f (x + s • y) + (u - s) * v := by
        linarith [hdiff, mul_comm v (u - s)]
      have hurs : (M - f (x + s • y)) / v ≤ u - s := by
        linarith
      have hineq : M - f (x + s • y) ≤ (u - s) * v := by
        have hmul := mul_le_mul_of_nonneg_right hurs (le_of_lt hvpos)
        have hvne : v ≠ 0 := ne_of_gt hvpos
        simpa [div_mul_eq_mul_div, hvne] using hmul
      have hM : M ≤ f (x + s • y) + (u - s) * v := by
        linarith
      have hfinal : M ≤ f (x + u • y) := le_trans hM hlinear
      exact (EReal.coe_le_coe_iff).2 hfinal
    have hlim_ge : ∀ M : ℝ,
        (M : EReal) ≤ Filter.liminf (fun t : ℝ => (f (x + t • y) : EReal)) Filter.atTop :=
      fun M =>
        Filter.le_liminf_of_le (f := Filter.atTop) (u := fun t : ℝ => (f (x + t • y) : EReal))
          (a := (M : EReal)) (h := hbound M)
    have hnot_top : Filter.liminf (fun t : ℝ => (f (x + t • y) : EReal)) Filter.atTop ≠
        (⊤ : EReal) := ne_of_lt hlim
    rcases (EReal.exists (p :=
        fun r => r = Filter.liminf (fun t : ℝ => (f (x + t • y) : EReal)) Filter.atTop)).1
      ⟨Filter.liminf (fun t : ℝ => (f (x + t • y) : EReal)) Filter.atTop, rfl⟩ with
      hbot | htop | hreal
    · have hcontr : (0 : EReal) ≤ (⊥ : EReal) := by simpa [hbot] using hlim_ge 0
      exact (not_le_of_gt (EReal.bot_lt_zero)) hcontr
    · exact (hnot_top htop.symm).elim
    · rcases hreal with ⟨r, hr⟩
      have hcontr : ((r + 1 : ℝ) : EReal) ≤ (r : EReal) := by
        simpa [hr] using hlim_ge (r + 1)
      have hcontr' : r + 1 ≤ r := (EReal.coe_le_coe_iff).1 hcontr
      linarith

/-- All ray functions are antitone iff the recession function is nonpositive. -/
lemma ray_antitone_all_iff_f0plus_le_zero_real {n : Nat}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)))
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal | ∃ x ∈ (Set.univ : Set (Fin n → Real)),
            r = ((f (x + y) - f x : Real) : EReal) }) {y : Fin n → Real} :
    (∀ x : Fin n → Real, Antitone (fun t : ℝ => f (x + t • y))) ↔ f0_plus y ≤ 0 := by
  have hrec :
      f0_plus y ≤ (0 : EReal) ↔
        ∀ x : Fin n → Real, ∀ t : ℝ, 0 < t →
          ((f (x + t • y) - f x) / t : Real) ≤ 0 :=
    recessionFunction_le_iff_ray (C := Set.univ) (f := f) (f0_plus := f0_plus) (hC := rfl) hf
      hf0_plus y 0
  simpa using
    (ray_antitone_all_iff_diffquotient_le_zero_real (f := f) (y := y)).trans hrec.symm

/-- For closed convex `f`, a ray antitone at one base point extends to all base points. -/
lemma ray_antitone_extend_closed_real {n : Nat} {f : (Fin n → Real) → Real} {y : Fin n → Real}
    (hclosed : ClosedConvexFunction (fun x => (f x : EReal)))
    (hx :
      ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)),
        Antitone (fun t : ℝ => f (x + t • y))) :
    ∀ x : Fin n → Real, Antitone (fun t : ℝ => f (x + t • y)) := by
  rcases hx with ⟨x0, _, hanti⟩
  have hbound : ∀ t > 0, ((f (x0 + t • y) - f x0) / t : Real) ≤ 0 := by
    intro t ht
    have hstep : f (x0 + t • y) ≤ f x0 := by
      simpa using (hanti (a := 0) (b := t) (le_of_lt ht))
    have hdiff : f (x0 + t • y) - f x0 ≤ 0 := by linarith
    have hquot : (f (x0 + t • y) - f x0) / t ≤ (0 : Real) :=
      (div_le_iff₀ ht).2 (by simpa using hdiff)
    simpa using hquot
  have hbound_all :
      ∀ x : Fin n → Real, ∀ t : Real, 0 < t →
        ((f (x + t • y) - f x) / t : Real) ≤ 0 :=
    ray_bound_extend_closed (f := f) (x0 := x0) (y := y) (v := 0) hclosed hbound
  exact (ray_antitone_all_iff_diffquotient_le_zero_real (f := f) (y := y)).2 hbound_all

/-- Theorem 8.6. Let `f` be a proper convex function, and let `y` be a vector. If
`lim_{λ → +∞} inf f (x + λ • y) < +∞` for a given `x`, then `f (x + λ • y)` is
non-increasing in `λ` for all real `λ`. This property holds for every `x` iff
`(f0^+)(y) ≤ 0`. When `f` is closed, this property holds for every `x` if it holds
for some `x ∈ dom f`. -/
theorem recessionFunction_ray_antitone_iff {n : Nat}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)))
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal | ∃ x ∈ (Set.univ : Set (Fin n → Real)),
            r = ((f (x + y) - f x : Real) : EReal) }) {y : Fin n → Real} :
    (∀ x : Fin n → Real,
        Filter.liminf (fun t : ℝ => (f (x + t • y) : EReal)) Filter.atTop < (⊤ : EReal) →
          Antitone (fun t : ℝ => f (x + t • y))) ∧
      ((∀ x : Fin n → Real, Antitone (fun t : ℝ => f (x + t • y))) ↔ f0_plus y ≤ 0) ∧
      (ClosedConvexFunction (fun x => (f x : EReal)) →
        (∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)),
          Antitone (fun t : ℝ => f (x + t • y))) →
        ∀ x : Fin n → Real, Antitone (fun t : ℝ => f (x + t • y))) := by
  refine ⟨?hlim, ?hiff, ?hclosed⟩
  · intro x hx
    exact ray_antitone_of_liminf_lt_top_real (hf := hf) (x := x) (y := y) hx
  · -- TODO: requires the recession formula tying `f0_plus` to `f`.
    exact ray_antitone_all_iff_f0plus_le_zero_real (hf := hf) (hf0_plus := hf0_plus) (y := y)
  · intro hclosed hx
    exact ray_antitone_extend_closed_real (f := f) (y := y) hclosed hx

/-- Antitone on the reverse ray yields monotone on the forward ray. -/
lemma ray_monotone_of_antitone_neg {n : Nat} {f : (Fin n → Real) → Real} {y : Fin n → Real} :
    (∀ x : Fin n → Real, Antitone (fun t : ℝ => f (x + t • (-y)))) →
      ∀ x : Fin n → Real, Monotone (fun t : ℝ => f (x + t • y)) := by
  intro h x s t hst
  have hanti := h x
  have hle :
      f (x + (-s) • (-y)) ≤ f (x + (-t) • (-y)) :=
    hanti (a := -t) (b := -s) (by simpa using (neg_le_neg hst))
  simpa [smul_neg, neg_smul, neg_neg] using hle

/-- Constancy along rays is equivalent to antitone behavior for `y` and `-y`. -/
lemma ray_const_iff_antitone_antitone_neg {n : Nat} {f : (Fin n → Real) → Real} {y : Fin n → Real} :
    (∀ x : Fin n → Real, ∀ s t : ℝ, f (x + s • y) = f (x + t • y)) ↔
      (∀ x : Fin n → Real, Antitone (fun t : ℝ => f (x + t • y))) ∧
        (∀ x : Fin n → Real, Antitone (fun t : ℝ => f (x + t • (-y)))) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x s t _
      simpa using (le_of_eq (h x t s))
    · intro x s t _
      have hEq : f (x + s • (-y)) = f (x + t • (-y)) := by
        have h' := h x (-s) (-t)
        simpa [smul_neg, neg_smul, neg_neg] using h'
      simpa using (le_of_eq hEq.symm)
  · intro h
    rcases h with ⟨hanti, hanti_neg⟩
    have hmono :
        ∀ x : Fin n → Real, Monotone (fun t : ℝ => f (x + t • y)) :=
      ray_monotone_of_antitone_neg (f := f) (y := y) hanti_neg
    intro x s t
    cases le_total s t with
    | inl hst =>
        have hle1 : f (x + t • y) ≤ f (x + s • y) := hanti x hst
        have hle2 : f (x + s • y) ≤ f (x + t • y) := hmono x hst
        exact le_antisymm hle2 hle1
    | inr hts =>
        have hle1 : f (x + s • y) ≤ f (x + t • y) := hanti x hts
        have hle2 : f (x + t • y) ≤ f (x + s • y) := hmono x hts
        exact le_antisymm hle1 hle2

/-- A uniform upper bound on a ray forces a finite liminf. -/
lemma liminf_lt_top_of_ray_bounded_above {n : Nat} {f : (Fin n → Real) → Real}
    {x y : Fin n → Real} {α : Real}
    (hbound : ∀ t : ℝ, (f (x + t • y) : EReal) ≤ (α : EReal)) :
    Filter.liminf (fun t : ℝ => (f (x + t • y) : EReal)) Filter.atTop < (⊤ : EReal) := by
  have hfreq :
      ∃ᶠ t in Filter.atTop, (f (x + t • y) : EReal) ≤ (α : EReal) :=
    Filter.Frequently.of_forall hbound
  have hlim_le :
      Filter.liminf (fun t : ℝ => (f (x + t • y) : EReal)) Filter.atTop ≤ (α : EReal) :=
    Filter.liminf_le_of_frequently_le' hfreq
  exact lt_of_le_of_lt hlim_le (by simp)

/-- Corollary 8.6.1. Let `f` be a proper convex function and `y` a vector. The function
`λ ↦ f (x + λ • y)` is constant on `ℝ` for every `x` if and only if `(f0^+)(y) ≤ 0` and
`(f0^+)(-y) ≤ 0`. When `f` is closed, this condition holds if there exists `x` and `α` such that
`f (x + λ • y) ≤ α` for all real `λ`. -/
theorem recessionFunction_ray_const_iff {n : Nat}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)))
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal | ∃ x ∈ (Set.univ : Set (Fin n → Real)),
            r = ((f (x + y) - f x : Real) : EReal) }) {y : Fin n → Real} :
    ((∀ x : Fin n → Real, ∀ s t : ℝ, f (x + s • y) = f (x + t • y)) ↔
        f0_plus y ≤ 0 ∧ f0_plus (-y) ≤ 0) ∧
      (ClosedConvexFunction (fun x => (f x : EReal)) →
        (∃ x : Fin n → Real, ∃ α : Real, ∀ t : Real, f (x + t • y) ≤ (α : EReal)) →
        f0_plus y ≤ 0 ∧ f0_plus (-y) ≤ 0) := by
  have htheorem_y :=
    recessionFunction_ray_antitone_iff (hf := hf) (hf0_plus := hf0_plus) (y := y)
  have htheorem_neg :=
    recessionFunction_ray_antitone_iff (hf := hf) (hf0_plus := hf0_plus) (y := -y)
  refine ⟨?hconst, ?hclosed⟩
  · constructor
    · intro hconst
      have hanti_pair :=
        (ray_const_iff_antitone_antitone_neg (f := f) (y := y)).1 hconst
      have hy : f0_plus y ≤ 0 := (htheorem_y.2.1).1 hanti_pair.1
      have hyneg : f0_plus (-y) ≤ 0 := (htheorem_neg.2.1).1 hanti_pair.2
      exact ⟨hy, hyneg⟩
    · intro hineq
      have hanti_pair :
          (∀ x : Fin n → Real, Antitone (fun t : ℝ => f (x + t • y))) ∧
            (∀ x : Fin n → Real, Antitone (fun t : ℝ => f (x + t • (-y)))) := by
        refine ⟨(htheorem_y.2.1).2 hineq.1, (htheorem_neg.2.1).2 hineq.2⟩
      exact (ray_const_iff_antitone_antitone_neg (f := f) (y := y)).2 hanti_pair
  · intro hclosed hbound
    rcases hbound with ⟨x0, α, hbound⟩
    have hlim :
        Filter.liminf (fun t : ℝ => (f (x0 + t • y) : EReal)) Filter.atTop < (⊤ : EReal) :=
      liminf_lt_top_of_ray_bounded_above (f := f) (x := x0) (y := y) (α := α) hbound
    have hanti_x0 : Antitone (fun t : ℝ => f (x0 + t • y)) :=
      htheorem_y.1 x0 hlim
    have hx0mem :
        x0 ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)) := by
      have hx0mem' :
          x0 ∈ (Set.univ : Set (Fin n → Real)) ∧ (f x0 : EReal) < (⊤ : EReal) := by
        refine ⟨by simp, ?_⟩
        exact (lt_top_iff_ne_top).2 (by simp)
      simp [effectiveDomain_eq, hx0mem']
    have hanti_all :
        ∀ x : Fin n → Real, Antitone (fun t : ℝ => f (x + t • y)) :=
      htheorem_y.2.2 hclosed ⟨x0, hx0mem, hanti_x0⟩
    have hy : f0_plus y ≤ 0 := (htheorem_y.2.1).1 hanti_all
    have hbound_neg : ∀ t : ℝ, (f (x0 + t • (-y)) : EReal) ≤ (α : EReal) := by
      intro t
      have h' := hbound (-t)
      simpa [smul_neg, neg_smul, neg_neg] using h'
    have hlim_neg :
        Filter.liminf (fun t : ℝ => (f (x0 + t • (-y)) : EReal)) Filter.atTop < (⊤ : EReal) :=
      liminf_lt_top_of_ray_bounded_above (f := f) (x := x0) (y := -y) (α := α) hbound_neg
    have hanti_x0_neg : Antitone (fun t : ℝ => f (x0 + t • (-y))) :=
      htheorem_neg.1 x0 hlim_neg
    have hanti_all_neg :
        ∀ x : Fin n → Real, Antitone (fun t : ℝ => f (x + t • (-y))) :=
      htheorem_neg.2.2 hclosed ⟨x0, hx0mem, hanti_x0_neg⟩
    have hyneg : f0_plus (-y) ≤ 0 := (htheorem_neg.2.1).1 hanti_all_neg
    exact ⟨hy, hyneg⟩

/-- The `toReal` of a convex `EReal` function is convex on any convex set where it is finite. -/
lemma convexOn_toReal_on_affine_of_finite {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunction f) {M : Set (Fin n → Real)} (hMconv : Convex ℝ M)
    (hfinite : ∀ x ∈ M, f x ≠ (⊥ : EReal) ∧ f x ≠ (⊤ : EReal)) :
    ConvexOn ℝ M (fun x => (f x).toReal) := by
  classical
  have hconv_epi_univ : Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) f) := by
    simpa [ConvexFunction, ConvexFunctionOn] using hf
  have hconv_fst :
      Convex ℝ ((LinearMap.fst ℝ (Fin n → Real) Real) ⁻¹' M) :=
    (Convex.linear_preimage (s := M) hMconv (LinearMap.fst ℝ (Fin n → Real) Real))
  have hEq :
      epigraph M f =
        ((LinearMap.fst ℝ (Fin n → Real) Real) ⁻¹' M) ∩
          epigraph (Set.univ : Set (Fin n → Real)) f := by
    ext p
    constructor
    · intro hp
      have hp' : p.1 ∈ M ∧ f p.1 ≤ (p.2 : EReal) := by
        simpa [epigraph] using hp
      refine ⟨?_, ?_⟩
      · simpa using hp'.1
      · change (p.1 ∈ (Set.univ : Set (Fin n → Real)) ∧ f p.1 ≤ (p.2 : EReal))
        exact ⟨by simp, hp'.2⟩
    · rintro ⟨hpM, hpE⟩
      have hpE' : f p.1 ≤ (p.2 : EReal) := by
        rcases (by simpa [epigraph] using hpE) with ⟨_, hpE'⟩
        exact hpE'
      change (p.1 ∈ M ∧ f p.1 ≤ (p.2 : EReal))
      exact ⟨hpM, hpE'⟩
  have hconvf : ConvexFunctionOn M f := by
    have hconv_epi :
        Convex ℝ (epigraph M f) := by
      have hconv_inter :
          Convex ℝ
            (((LinearMap.fst ℝ (Fin n → Real) Real) ⁻¹' M) ∩
              epigraph (Set.univ : Set (Fin n → Real)) f) :=
        hconv_fst.inter hconv_epi_univ
      simpa [hEq] using hconv_inter
    simpa [ConvexFunctionOn] using hconv_epi
  have hnotbot : ∀ x ∈ M, f x ≠ (⊥ : EReal) := by
    intro x hx
    exact (hfinite x hx).1
  have hseg :=
    (convexFunctionOn_iff_segment_inequality (C := M) (f := f) hMconv hnotbot).1 hconvf
  refine (convexOn_iff_forall_pos).2 ?_
  refine ⟨hMconv, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb_lt : b < 1 := by linarith
  have ha_eq : a = 1 - b := by linarith
  have hseg' :
      f ((1 - b) • x + b • y) ≤
        ((1 - b : Real) : EReal) * f x + ((b : Real) : EReal) * f y :=
    hseg x hx y hy b hb hb_lt
  have hx' : (1 - b) • x + b • y ∈ M := by
    have h1 : 0 ≤ (1 - b) := by linarith
    have hsum : (1 - b) + b = 1 := by ring
    exact hMconv hx hy h1 hb.le hsum
  have hbot :
      f ((1 - b) • x + b • y) ≠ (⊥ : EReal) :=
    (hfinite _ hx').1
  have hfx_bot : f x ≠ (⊥ : EReal) := (hfinite x hx).1
  have hfy_bot : f y ≠ (⊥ : EReal) := (hfinite y hy).1
  have hfx_top : f x ≠ (⊤ : EReal) := (hfinite x hx).2
  have hfy_top : f y ≠ (⊤ : EReal) := (hfinite y hy).2
  have hfx_coe : ((f x).toReal : EReal) = f x :=
    EReal.coe_toReal hfx_top hfx_bot
  have hfy_coe : ((f y).toReal : EReal) = f y :=
    EReal.coe_toReal hfy_top hfy_bot
  have hsum :
      ((1 - b : Real) : EReal) * f x + ((b : Real) : EReal) * f y =
        (( (1 - b) * (f x).toReal + b * (f y).toReal : Real) : EReal) := by
    calc
      ((1 - b : Real) : EReal) * f x + ((b : Real) : EReal) * f y =
          ((1 - b : Real) : EReal) * ((f x).toReal : EReal) +
            ((b : Real) : EReal) * ((f y).toReal : EReal) := by
            simp [hfx_coe, hfy_coe]
      _ = (( (1 - b) * (f x).toReal : Real) : EReal) +
            ((b * (f y).toReal : Real) : EReal) := by
            simp [EReal.coe_mul]
      _ = (( (1 - b) * (f x).toReal + b * (f y).toReal : Real) : EReal) := by
            simp
  have hsum_not_top :
      ((1 - b : Real) : EReal) * f x + ((b : Real) : EReal) * f y ≠ (⊤ : EReal) := by
    rw [hsum]
    exact EReal.coe_ne_top _
  have hsum_toReal :
      (((1 - b : Real) : EReal) * f x + ((b : Real) : EReal) * f y).toReal =
        (1 - b) * (f x).toReal + b * (f y).toReal := by
    have hsum' := congrArg EReal.toReal hsum
    simpa using hsum'
  have hineq :
      (f ((1 - b) • x + b • y)).toReal ≤
        ( (1 - b) * (f x).toReal + b * (f y).toReal ) := by
    have hsum_toReal' :
        (((1 - (b : EReal)) * f x + (b : EReal) * f y).toReal =
          (1 - b) * (f x).toReal + b * (f y).toReal) := by
      simpa [EReal.coe_sub] using hsum_toReal
    have h := EReal.toReal_le_toReal hseg' hbot hsum_not_top
    simpa [hsum_toReal'] using h
  simpa [ha_eq] using hineq

/-- A convex real function bounded above on `ℝ` is antitone. -/
lemma convexOn_real_antitone_of_bddAbove {g : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ g) (hbounded : ∃ α, ∀ t, g t ≤ α) :
    Antitone g := by
  rcases hbounded with ⟨α, hα⟩
  intro s t hst
  by_cases hEq : s = t
  · subst hEq
    exact le_rfl
  · have hlt : s < t := lt_of_le_of_ne hst hEq
    by_contra hgt
    have hgt' : g s < g t := lt_of_not_ge hgt
    set m : ℝ := (g t - g s) / (t - s)
    have hmpos : 0 < m := by
      have hnum : 0 < g t - g s := sub_pos.mpr hgt'
      have hden : 0 < t - s := sub_pos.mpr hlt
      exact div_pos hnum hden
    set u : ℝ := t + (α - g t) / m + 1
    have htu : t < u := by
      have hnum : 0 ≤ α - g t := sub_nonneg.mpr (hα t)
      have hdiv : 0 ≤ (α - g t) / m := by
        exact div_nonneg hnum (le_of_lt hmpos)
      have hpos : 0 < (α - g t) / m + 1 := by linarith
      have hdiff : u - t = (α - g t) / m + 1 := by
        simp [u, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      have : 0 < u - t := by
        simpa [hdiff] using hpos
      exact (sub_pos).1 this
    have hmono :=
      ConvexOn.slope_mono_adjacent (f := g) hconv (by simp) (by simp) hlt htu
    have hbound : (g u - g t) / (u - t) ≤ (α - g t) / (u - t) := by
      have hgu : g u ≤ α := hα u
      have hgu' : g u - g t ≤ α - g t := sub_le_sub_right hgu (g t)
      have hden : 0 ≤ u - t := sub_nonneg.mpr (le_of_lt htu)
      exact div_le_div_of_nonneg_right hgu' hden
    have hle : m ≤ (α - g t) / (u - t) := by
      have hle' : (g t - g s) / (t - s) ≤ (α - g t) / (u - t) :=
        le_trans hmono hbound
      simpa [m] using hle'
    have hdiff : u - t = (α - g t) / m + 1 := by
      simp [u, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hden_pos : 0 < u - t := sub_pos.mpr htu
    have hmne : m ≠ 0 := by
      simpa [ne_comm] using (ne_of_gt hmpos)
    have hmul_div : m * ((α - g t) / m) = α - g t := by
      field_simp [hmne]
    have hmul : m * (u - t) = (α - g t) + m := by
      calc
        m * (u - t) = m * ((α - g t) / m + 1) := by
          simp [hdiff]
        _ = m * ((α - g t) / m) + m := by ring
        _ = (α - g t) + m := by
          simp [hmul_div]
    have hcalc : (α - g t) < m * (u - t) := by
      have hlt' : (α - g t) < (α - g t) + m := by linarith
      simpa [hmul] using hlt'
    have hbound_lt : (α - g t) / (u - t) < m :=
      (div_lt_iff₀ hden_pos).2 hcalc
    have hmcontra : m < m := lt_of_le_of_lt hle hbound_lt
    exact (lt_irrefl _ hmcontra)

/-- A convex real function bounded above on `ℝ` is constant. -/
lemma convexOn_real_const_of_bddAbove {g : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ g) (hbounded : ∃ α, ∀ t, g t ≤ α) :
    ∀ s t, g s = g t := by
  have hanti : Antitone g :=
    convexOn_real_antitone_of_bddAbove (g := g) hconv hbounded
  let negAff : ℝ →ᵃ[ℝ] ℝ := (-(LinearMap.id : ℝ →ₗ[ℝ] ℝ)).toAffineMap
  have hconv_neg : ConvexOn ℝ Set.univ (fun x => g (-x)) := by
    simpa [negAff] using
      (ConvexOn.comp_affineMap (f := g) (g := negAff) (s := (Set.univ : Set ℝ)) hconv)
  have hbounded_neg : ∃ α, ∀ t, g (-t) ≤ α := by
    rcases hbounded with ⟨α, hα⟩
    exact ⟨α, by intro t; simpa using hα (-t)⟩
  have hanti_neg : Antitone (fun x => g (-x)) :=
    convexOn_real_antitone_of_bddAbove (g := fun x => g (-x)) hconv_neg hbounded_neg
  have hmono : Monotone g := by
    intro s t hst
    have h := hanti_neg (a := -t) (b := -s) (by simpa using (neg_le_neg hst))
    simpa using h
  intro s t
  cases le_total s t with
  | inl hst =>
      exact le_antisymm (hmono hst) (hanti hst)
  | inr hts =>
      exact le_antisymm (hanti hts) (hmono hts)

/-- A bounded-above convex function is constant along any line in an affine set where it is
finite. -/
lemma line_const_of_bddAbove_on_affine {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunction f) (M : AffineSubspace Real (Fin n → Real))
    (hfinite :
      ∀ x ∈ (M : Set (Fin n → Real)), f x ≠ (⊥ : EReal) ∧ f x ≠ (⊤ : EReal))
    (hbounded : ∃ α : Real, ∀ x ∈ (M : Set (Fin n → Real)), f x ≤ (α : EReal))
    {x0 x : Fin n → Real} (hx0 : x0 ∈ (M : Set (Fin n → Real)))
    (hx : x ∈ (M : Set (Fin n → Real))) :
    ∀ s t : ℝ, f (AffineMap.lineMap x0 x s) = f (AffineMap.lineMap x0 x t) := by
  let L : ℝ →ᵃ[ℝ] (Fin n → Real) := AffineMap.lineMap x0 x
  have hline_mem : ∀ t : ℝ, L t ∈ (M : Set (Fin n → Real)) := by
    intro t
    simpa [L] using (AffineMap.lineMap_mem (Q := M) t hx0 hx)
  have hconv_M : Convex ℝ (M : Set (Fin n → Real)) := M.convex
  have hconv_toReal :
      ConvexOn ℝ (M : Set (Fin n → Real)) (fun z => (f z).toReal) :=
    convexOn_toReal_on_affine_of_finite (hf := hf) (M := (M : Set _)) hconv_M hfinite
  have hpreim : L ⁻¹' (M : Set (Fin n → Real)) = Set.univ := by
    ext t
    constructor
    · intro _; simp
    · intro _
      exact hline_mem t
  have hconv_line : ConvexOn ℝ Set.univ (fun t => (f (L t)).toReal) := by
    have hconv' :=
      (ConvexOn.comp_affineMap (f := fun z => (f z).toReal) (g := L)
        (s := (M : Set (Fin n → Real))) hconv_toReal)
    simpa [hpreim, L] using hconv'
  rcases hbounded with ⟨α, hα⟩
  have hbounded_line : ∀ t : ℝ, (f (L t)).toReal ≤ α := by
    intro t
    have htM : L t ∈ (M : Set (Fin n → Real)) := hline_mem t
    have hle : f (L t) ≤ (α : EReal) := hα _ htM
    have hbot : f (L t) ≠ (⊥ : EReal) := (hfinite _ htM).1
    have htop : (α : EReal) ≠ (⊤ : EReal) := EReal.coe_ne_top _
    have hle' := EReal.toReal_le_toReal hle hbot htop
    simpa using hle'
  have hconst :
      ∀ s t : ℝ, (f (L s)).toReal = (f (L t)).toReal :=
    convexOn_real_const_of_bddAbove (g := fun t => (f (L t)).toReal) hconv_line
      ⟨α, hbounded_line⟩
  intro s t
  have hEq : (f (L s)).toReal = (f (L t)).toReal := hconst s t
  have hsM : L s ∈ (M : Set (Fin n → Real)) := hline_mem s
  have htM : L t ∈ (M : Set (Fin n → Real)) := hline_mem t
  have hbot_s : f (L s) ≠ (⊥ : EReal) := (hfinite _ hsM).1
  have htop_s : f (L s) ≠ (⊤ : EReal) := (hfinite _ hsM).2
  have hbot_t : f (L t) ≠ (⊥ : EReal) := (hfinite _ htM).1
  have htop_t : f (L t) ≠ (⊤ : EReal) := (hfinite _ htM).2
  calc
    f (L s) = ((f (L s)).toReal : EReal) := (EReal.coe_toReal htop_s hbot_s).symm
    _ = ((f (L t)).toReal : EReal) := by simp [hEq]
    _ = f (L t) := EReal.coe_toReal htop_t hbot_t

end Section08
end Chap02
