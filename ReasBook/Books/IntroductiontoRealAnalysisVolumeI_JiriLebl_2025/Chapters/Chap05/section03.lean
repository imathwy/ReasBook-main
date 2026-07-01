/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import Mathlib

open MeasureTheory
open scoped Topology

section Chap05
section Section03

/-- Theorem 5.3.1 (Fundamental theorem of calculus, first form). If `F` is
continuous on `[a, b]`, differentiable on `(a, b)` with derivative `f`, and
`f` is Riemann integrable on `[a, b]`, then `∫_{a}^{b} f = F b - F a`. -/
theorem intervalIntegral_deriv_eq_sub {a b : ℝ} {F f : ℝ → ℝ}
    (hab : a ≤ b)
    (hcont : ContinuousOn F (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt F (f x) x)
    (hinteg : IntervalIntegrable f volume a b) :
    ∫ x in a..b, f x = F b - F a := by
  simpa using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := a) (b := b) (f := F)
      (f' := f) hab hcont hderiv hinteg)

/-- Example 5.3.2: By the fundamental theorem of calculus,
`∫_0^1 x^2 \\, dx = 1 / 3` using the antiderivative `x ↦ x^3 / 3`. -/
lemma integral_square_unit_interval :
    ∫ x in (0 : ℝ)..1, x^2 = (1 : ℝ) / 3 := by
  have hcont : ContinuousOn (fun x : ℝ => x^3 / 3) (Set.Icc (0 : ℝ) 1) := by
    simpa using ((continuous_pow 3).div_const (3 : ℝ)).continuousOn
  have hderiv :
      ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x^3 / 3) (x^2) x := by
    intro x _
    have h3 : (3 : ℝ) ≠ 0 := by norm_num
    simpa [h3] using (hasDerivAt_pow 3 x).div_const (3 : ℝ)
  have hinteg : IntervalIntegrable (fun x : ℝ => x^2) volume (0 : ℝ) 1 := by
    simp
  have hab : (0 : ℝ) ≤ 1 := by norm_num
  have h :=
    intervalIntegral_deriv_eq_sub (a := 0) (b := 1)
      (F := fun x : ℝ => x^3 / 3) (f := fun x : ℝ => x^2) hab hcont hderiv hinteg
  simpa using h

/-- Theorem 5.3.3 (Fundamental theorem of calculus, second form). If `f` is
Riemann integrable on `[a, b]` and `F x = ∫_{a}^{x} f`, then `F` is continuous
on `[a, b]`, and whenever `f` is continuous at `c ∈ (a, b)` the function `F`
is differentiable at `c` with derivative `F' c = f c`. -/
theorem fundamental_theorem_of_calculus_second
    {a b : ℝ} {f : ℝ → ℝ}
    (hinteg : IntervalIntegrable f volume a b) :
    ContinuousOn (fun x => ∫ t in a..x, f t) (Set.Icc a b) ∧
      ∀ {c}, c ∈ Set.Ioo a b → ContinuousAt f c →
        HasDerivAt (fun x => ∫ t in a..x, f t) (f c) c := by
  have hint : IntegrableOn f (Set.uIcc a b) volume :=
    (intervalIntegrable_iff' (f := f) (μ := volume) (a := a) (b := b)).1 hinteg
  have hcont_u :
      ContinuousOn (fun x => ∫ t in a..x, f t) (Set.uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := f) hint
  have hcont :
      ContinuousOn (fun x => ∫ t in a..x, f t) (Set.Icc a b) :=
    hcont_u.mono Set.Icc_subset_uIcc
  refine ⟨hcont, ?_⟩
  intro c hc hcontc
  have hc' : c ∈ Set.uIcc a b := Set.mem_uIcc_of_le hc.1.le hc.2.le
  have hsub : Set.uIcc a c ⊆ Set.uIcc a b :=
    Set.uIcc_subset_uIcc_left hc'
  have hint_ac : IntervalIntegrable f volume a c := hinteg.mono_set hsub
  have hmem : Set.uIcc a b ∈ 𝓝 c := by
    have hab : a < b := lt_trans hc.1 hc.2
    simpa [Set.uIcc_of_lt hab] using (Icc_mem_nhds hc.1 hc.2)
  have hmeas : StronglyMeasurableAtFilter f (𝓝 c) := by
    refine AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem ?_ hmem
    exact hint.integrable.aestronglyMeasurable
  exact intervalIntegral.integral_hasDerivAt_right hint_ac hmeas hcontc

/-- Theorem 5.3.5 (Change of variables). If `g : [a,b] → ℝ` is continuously differentiable
and maps `[a,b]` into `[c,d]`, and `f : [c,d] → ℝ` is continuous, then
`∫_{a}^{b} f (g x) * g' x = ∫_{g a}^{g b} f`. -/
theorem intervalIntegral_change_of_variables
    {a b c d : ℝ} {f g : ℝ → ℝ}
    (hab : a ≤ b)
    (hg_diff : ContDiffOn ℝ 1 g (Set.Icc a b))
    (hf_cont : ContinuousOn f (Set.Icc c d))
    (hg_maps : Set.MapsTo g (Set.Icc a b) (Set.Icc c d)) :
    ∫ x in a..b, f (g x) * deriv g x = ∫ s in g a..g b, f s := by
  classical
  by_cases hlt : a < b
  · have hcont_g : ContinuousOn g (Set.uIcc a b) := by
      simpa [Set.uIcc_of_le hab] using hg_diff.continuousOn
    have hdiff_on : DifferentiableOn ℝ g (Set.Icc a b) :=
      hg_diff.differentiableOn_one
    have hderiv :
        ∀ x ∈ Set.Ioo (min a b) (max a b),
          HasDerivWithinAt g (derivWithin g (Set.Icc a b) x) (Set.Ioi x) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo a b := by
        simpa [min_eq_left hab, max_eq_right hab] using hx
      have hxIcc : x ∈ Set.Icc a b := ⟨hx'.1.le, hx'.2.le⟩
      have hdiffWithin : DifferentiableWithinAt ℝ g (Set.Icc a b) x := hdiff_on x hxIcc
      have hnhds : Set.Icc a b ∈ 𝓝 x := Icc_mem_nhds hx'.1 hx'.2
      have hdiffAt : DifferentiableAt ℝ g x := hdiffWithin.differentiableAt hnhds
      have hderivAt : HasDerivAt g (deriv g x) x := hdiffAt.hasDerivAt
      have hderivWithin : HasDerivWithinAt g (deriv g x) (Set.Ioi x) x :=
        hderivAt.hasDerivWithinAt
      have hderiv_eq : derivWithin g (Set.Icc a b) x = deriv g x :=
        derivWithin_of_mem_nhds hnhds
      simpa [hderiv_eq] using hderivWithin
    have hcont_deriv :
        ContinuousOn (derivWithin g (Set.Icc a b)) (Set.uIcc a b) := by
      have h' :=
        hg_diff.continuousOn_derivWithin (uniqueDiffOn_Icc hlt)
          (by simp : (1 : WithTop ℕ∞) ≤ (1 : WithTop ℕ∞))
      simpa [Set.uIcc_of_le hab] using h'
    have hcont_f : ContinuousOn f (g '' Set.uIcc a b) := by
      refine hf_cont.mono ?_
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hx' : x ∈ Set.Icc a b := by
        simpa [Set.uIcc_of_le hab] using hx
      exact hg_maps hx'
    have hmain :
        (∫ x in a..b, f (g x) * derivWithin g (Set.Icc a b) x) =
          ∫ s in g a..g b, f s := by
      simpa [Function.comp] using
        (intervalIntegral.integral_comp_mul_deriv'' (a := a) (b := b)
          (f := g) (f' := derivWithin g (Set.Icc a b)) (g := f)
          hcont_g hderiv hcont_deriv hcont_f)
    have hderiv_ae :
        ∀ᵐ x ∂volume, x ∈ Set.uIoc a b →
          f (g x) * derivWithin g (Set.Icc a b) x = f (g x) * deriv g x := by
      refine (ae_uIoc_iff).2 ?_
      refine ⟨?_, ?_⟩
      · have h_ne_b : ∀ᵐ x ∂volume, x ≠ b := by
          simp [ae_iff, measure_singleton]
        refine h_ne_b.mono ?_
        intro x hxne hxIoc
        have hxIoo : x ∈ Set.Ioo a b :=
          ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxne⟩
        have h_eq : derivWithin g (Set.Icc a b) x = deriv g x :=
          derivWithin_of_mem_nhds (Icc_mem_nhds hxIoo.1 hxIoo.2)
        simp [h_eq]
      · have hnot : ¬ b < a := not_lt_of_ge hab
        simp [Set.Ioc_eq_empty hnot]
    have hcongr :
        ∫ x in a..b, f (g x) * derivWithin g (Set.Icc a b) x =
          ∫ x in a..b, f (g x) * deriv g x := by
      refine intervalIntegral.integral_congr_ae hderiv_ae
    calc
      ∫ x in a..b, f (g x) * deriv g x =
          ∫ x in a..b, f (g x) * derivWithin g (Set.Icc a b) x := by
            symm
            exact hcongr
      _ = ∫ s in g a..g b, f s := hmain
  · have hEq : a = b := le_antisymm hab (not_lt.mp hlt)
    subst hEq
    simp

/-- Example 5.3.6: Using the substitution `g(x) = x^2` and that the derivative of `sin` is `cos`,
`∫_0^{√π} x * cos (x^2) = 0`. -/
lemma integral_mul_cos_square_root_pi :
    ∫ x in (0 : ℝ)..Real.sqrt Real.pi, x * Real.cos (x^2) = 0 := by
  have hab : (0 : ℝ) ≤ Real.sqrt Real.pi := by
    exact Real.sqrt_nonneg _
  have hg_diff :
      ContDiffOn ℝ 1 (fun x : ℝ => x^2) (Set.Icc (0 : ℝ) (Real.sqrt Real.pi)) := by
    simpa using
      ((contDiff_id : ContDiff ℝ 1 (fun x : ℝ => x)).pow 2).contDiffOn
  have hf_cont :
      ContinuousOn (fun s : ℝ => Real.cos s / 2) (Set.Icc (0 : ℝ) Real.pi) := by
    simpa using ((Real.continuous_cos.div_const (2 : ℝ)).continuousOn)
  have hg_maps :
      Set.MapsTo (fun x : ℝ => x^2) (Set.Icc (0 : ℝ) (Real.sqrt Real.pi))
        (Set.Icc (0 : ℝ) Real.pi) := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hxle : x ≤ Real.sqrt Real.pi := hx.2
    have hpi0 : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    have hx2le : x^2 ≤ (Real.sqrt Real.pi)^2 := by
      have hsqrt0 : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
      have hx2le' : x * x ≤ Real.sqrt Real.pi * Real.sqrt Real.pi :=
        mul_le_mul hxle hxle hx0 hsqrt0
      simpa [pow_two] using hx2le'
    have hx2le_pi : x^2 ≤ Real.pi := by
      have hsq : (Real.sqrt Real.pi)^2 = Real.pi := by
        simpa using (Real.sq_sqrt (hpi0))
      simpa [hsq] using hx2le
    exact ⟨sq_nonneg x, hx2le_pi⟩
  have hderiv : ∀ x : ℝ, deriv (fun x : ℝ => x^2) x = 2 * x := by
    intro x
    simp
  have hfun :
      (fun x : ℝ => (Real.cos (x^2) / 2) * deriv (fun x : ℝ => x^2) x) =
        fun x => x * Real.cos (x^2) := by
    funext x
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    calc
      (Real.cos (x^2) / 2) * deriv (fun x : ℝ => x^2) x
          = (Real.cos (x^2) / 2) * (2 * x) := by simp [hderiv x]
      _ = Real.cos (x^2) * x := by
            field_simp [htwo, mul_comm, mul_left_comm, mul_assoc]
      _ = x * Real.cos (x^2) := by ring
  have hchange :
      ∫ x in (0 : ℝ)..Real.sqrt Real.pi, x * Real.cos (x^2) =
        ∫ s in (0 : ℝ)..Real.pi, Real.cos s / 2 := by
    have h :=
      intervalIntegral_change_of_variables (a := 0) (b := Real.sqrt Real.pi)
        (c := 0) (d := Real.pi) (f := fun s : ℝ => Real.cos s / 2)
        (g := fun x : ℝ => x^2) hab hg_diff hf_cont hg_maps
    have hpi0 : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    have hzero : (fun x : ℝ => x^2) 0 = 0 := by norm_num
    have hsq : (fun x : ℝ => x^2) (Real.sqrt Real.pi) = Real.pi := by
      simpa using (Real.sq_sqrt (hpi0))
    rw [hzero, hsq] at h
    have hcongr :
        ∀ᵐ x : ℝ,
          x ∈ Set.uIoc (0 : ℝ) (Real.sqrt Real.pi) →
            x * Real.cos (x^2) =
              (Real.cos (x^2) / 2) * deriv (fun x : ℝ => x^2) x := by
      refine ae_of_all (μ := volume) ?_
      intro x _
      simpa using (congrArg (fun f => f x) hfun).symm
    calc
      ∫ x in (0 : ℝ)..Real.sqrt Real.pi, x * Real.cos (x^2) =
          ∫ x in (0 : ℝ)..Real.sqrt Real.pi,
            (Real.cos (x^2) / 2) * deriv (fun x : ℝ => x^2) x := by
            exact intervalIntegral.integral_congr_ae hcongr
      _ = ∫ s in (0 : ℝ)..Real.pi, Real.cos s / 2 := h
  have hcos_int : ∫ s in (0 : ℝ)..Real.pi, Real.cos s / 2 = 0 := by
    have hcont :
        ContinuousOn (fun s : ℝ => Real.sin s / 2) (Set.Icc (0 : ℝ) Real.pi) := by
      simpa using ((Real.continuous_sin.div_const (2 : ℝ)).continuousOn)
    have hderiv2 :
        ∀ s ∈ Set.Ioo (0 : ℝ) Real.pi,
          HasDerivAt (fun s : ℝ => Real.sin s / 2) (Real.cos s / 2) s := by
      intro s _
      simpa using (Real.hasDerivAt_sin s).div_const (2 : ℝ)
    have hcos_int' :
        IntervalIntegrable (fun s : ℝ => Real.cos s / 2) volume (0 : ℝ) Real.pi := by
      simp [div_eq_mul_inv]
    have h :=
      intervalIntegral_deriv_eq_sub (a := 0) (b := Real.pi)
        (F := fun s : ℝ => Real.sin s / 2) (f := fun s : ℝ => Real.cos s / 2)
        (hab := le_of_lt Real.pi_pos) hcont hderiv2 hcos_int'
    calc
      ∫ s in (0 : ℝ)..Real.pi, Real.cos s / 2 =
          Real.sin Real.pi / 2 - Real.sin 0 / 2 := h
      _ = 0 := by simp [Real.sin_pi, Real.sin_zero]
  calc
    ∫ x in (0 : ℝ)..Real.sqrt Real.pi, x * Real.cos (x^2) =
        ∫ s in (0 : ℝ)..Real.pi, Real.cos s / 2 := hchange
    _ = 0 := hcos_int

/-- Example 5.3.7: The naive substitution `g x = log |x|` for
`∫_{-1}^{1} (log |x|) / x` fails because the integrand is unbounded and not
continuous at `0`, so the integral over `[-1,1]` is not well-defined as a
Riemann (Lebesgue) integral. -/
lemma not_integrable_log_abs_div_x_on_neg_one_one :
    ¬ MeasureTheory.IntegrableOn (fun x : ℝ => Real.log (|x|) / x) (Set.Icc (-1 : ℝ) 1) := by
  have hlog_tendsto :
      Filter.Tendsto (fun x => ‖Real.log (|x|)‖) (𝓝[≠] (0 : ℝ)) Filter.atTop := by
    simpa [Real.log_abs, Real.norm_eq_abs] using
      (Filter.tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsNE_zero))
  have hlog_eventually :
      ∀ᶠ x in 𝓝[≠] (0 : ℝ), (1 : ℝ) ≤ ‖Real.log (|x|)‖ :=
    hlog_tendsto.eventually_ge_atTop 1
  have hbigO :
      (fun x : ℝ => x⁻¹) =O[𝓝[≠] (0 : ℝ)] (fun x => Real.log (|x|) / x) := by
    refine Asymptotics.IsBigO.of_bound (1 : ℝ) ?_
    filter_upwards [hlog_eventually] with x hx
    have hx' : (1 : ℝ) ≤ |Real.log (|x|)| := by
      simpa [Real.norm_eq_abs] using hx
    have hdiv : (1 : ℝ) / |x| ≤ |Real.log (|x|)| / |x| :=
      div_le_div_of_nonneg_right hx' (abs_nonneg x)
    have hineq : ‖x⁻¹‖ ≤ ‖Real.log (|x|) / x‖ := by
      simpa [Real.norm_eq_abs, abs_div, abs_inv, one_div] using hdiv
    simpa using hineq
  have hnot_interval :
      ¬ IntervalIntegrable (fun x : ℝ => Real.log (|x|) / x) volume (-1) 1 := by
    refine not_intervalIntegrable_of_sub_inv_isBigO_punctured (c := (0 : ℝ)) ?_ (by norm_num) ?_
    · simpa using hbigO
    · exact Set.mem_uIcc_of_le (by norm_num) (by norm_num)
  intro h_integrable
  have hab : (-1 : ℝ) ≤ 1 := by norm_num
  have hinterval :
      IntervalIntegrable (fun x : ℝ => Real.log (|x|) / x) volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume)
      (f := fun x : ℝ => Real.log (|x|) / x) hab).2 h_integrable
  exact hnot_interval hinterval

end Section03
end Chap05
