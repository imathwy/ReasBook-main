import Mathlib
import DifferentialForms_Cartan_1970.III.section12.SectorArc

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the core owner is the chapter-local `sectorArcIntegral`, while the
-- source-facing Jordan-lemma integrand should use the complex-valued bridge
-- `sectorArcIntegral_def` rather than the parameterization-derivative implementation of that
-- owner. The statement shape was checked against `SectorArc`, the earlier sector-arc convergence
-- surface in `0002_Lemma_1.lean`, and mathlib's `TendstoUniformlyOn` / interval-integral API.

noncomputable section

open scoped Interval

/-- Helper for Lemma 3: on the upper semicircle, the damping integral
`∫_0^π exp (-r sin θ) r dθ` is bounded above by `π`. -/
theorem exp_neg_sin_mul_intervalIntegral_le_pi
    {r : ℝ} (hr : 0 ≤ r) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.exp (-r * Real.sin θ) * r ≤ Real.pi := by
  let g : ℝ → ℝ := fun θ ↦ Real.exp (-r * Real.sin θ) * r
  have hg_cont : Continuous g := by
    -- The damping kernel is continuous on the whole semicircle.
    fun_prop
  have hg_int_left : IntervalIntegrable g MeasureTheory.volume 0 (Real.pi / 2) := by
    exact hg_cont.intervalIntegrable _ _
  have hg_int_right : IntervalIntegrable g MeasureTheory.volume (Real.pi / 2) Real.pi := by
    exact hg_cont.intervalIntegrable _ _
  have hsymm :
      ∫ θ in (Real.pi / 2)..Real.pi, g θ = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
    -- Reflect the second half of the interval using `θ ↦ π - θ`.
    calc
      ∫ θ in (Real.pi / 2)..Real.pi, g θ
          = ∫ θ in (Real.pi / 2)..Real.pi, g (Real.pi - θ) := by
            refine intervalIntegral.integral_congr_ae ?_
            filter_upwards with θ
            simp [g, Real.sin_pi_sub]
      _ = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
            have hpi_half : Real.pi - Real.pi / 2 = Real.pi / 2 := by
              ring
            rw [intervalIntegral.integral_comp_sub_left]
            simp [hpi_half]
  have hleft_bound : ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ ≤ Real.pi / 2 := by
    have hcomparison_int :
        IntervalIntegrable
          (fun θ : ℝ ↦ Real.exp (-(2 / Real.pi * r) * θ) * r)
          MeasureTheory.volume
          0
          (Real.pi / 2) := by
      -- The comparison kernel is also continuous on the compact interval.
      have hcomparison_cont :
          Continuous (fun θ : ℝ ↦ Real.exp (-(2 / Real.pi * r) * θ) * r) := by
        fun_prop
      exact hcomparison_cont.intervalIntegrable _ _
    have hcomparison :
        ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ ≤
          ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp (-(2 / Real.pi * r) * θ) * r := by
      -- Jordan's inequality gives the linear lower bound on `sin`.
      refine intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := Real.pi / 2)
        (by positivity) hg_int_left hcomparison_int ?_
      intro θ hθ
      have hsin : 2 / Real.pi * θ ≤ Real.sin θ :=
        Real.mul_le_sin hθ.1 hθ.2
      have hexp :
          Real.exp (-r * Real.sin θ) ≤ Real.exp (-(2 / Real.pi * r) * θ) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hsin, hr]
      exact mul_le_mul_of_nonneg_right hexp hr
    rcases eq_or_lt_of_le hr with rfl | hrpos
    · simpa [g]
        using (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
    · let c : ℝ := -(2 / Real.pi * r)
      have hc : c ≠ 0 := by
        dsimp [c]
        exact neg_ne_zero.mpr <| mul_ne_zero (div_ne_zero two_ne_zero Real.pi_ne_zero) hrpos.ne'
      have hc_pi : c * (Real.pi / 2) = -r := by
        dsimp [c]
        field_simp [Real.pi_ne_zero]
      have hrc : r * c⁻¹ = -(Real.pi / 2) := by
        dsimp [c]
        field_simp [Real.pi_ne_zero, hrpos.ne']
      calc
        ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ
            ≤ ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp (c * θ) * r := by
                simpa [g, c] using hcomparison
        _ = r * ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp (c * θ) := by
              rw [intervalIntegral.integral_mul_const]
              ring
        _ = r * (c⁻¹ * ∫ x in c * (0 : ℝ)..c * (Real.pi / 2), Real.exp x) := by
              simpa [smul_eq_mul] using
                congrArg (fun x : ℝ => r * x)
                  (intervalIntegral.integral_comp_mul_left (f := Real.exp) (a := (0 : ℝ))
                    (b := Real.pi / 2) (c := c) hc)
        _ = r * (c⁻¹ * (Real.exp (c * (Real.pi / 2)) - 1)) := by
              rw [integral_exp, mul_zero, Real.exp_zero]
        _ = Real.pi / 2 * (1 - Real.exp (-r)) := by
              rw [hc_pi]
              calc
                r * (c⁻¹ * (Real.exp (-r) - 1))
                    = (r * c⁻¹) * (Real.exp (-r) - 1) := by ring
                _ = -(Real.pi / 2) * (Real.exp (-r) - 1) := by rw [hrc]
                _ = Real.pi / 2 * (1 - Real.exp (-r)) := by ring
        _ ≤ Real.pi / 2 := by
              have hexp_nonneg : 0 ≤ Real.exp (-r) := Real.exp_nonneg (-r)
              nlinarith [Real.pi_pos]
  have hsplit :
      (∫ θ in (0 : ℝ)..(Real.pi / 2), g θ) + ∫ θ in (Real.pi / 2)..Real.pi, g θ =
        ∫ θ in (0 : ℝ)..Real.pi, g θ := by
    -- Split the upper semicircle into the two symmetric halves.
    simpa using intervalIntegral.integral_add_adjacent_intervals hg_int_left hg_int_right
  have hdouble :
      2 * ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ ≤ 2 * (Real.pi / 2) := by
    linarith [hleft_bound]
  let I : ℝ := ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ
  have hIbound : 2 * I ≤ 2 * (Real.pi / 2) := by
    simpa [I] using hdouble
  calc
    ∫ θ in (0 : ℝ)..Real.pi, g θ
        = I + ∫ θ in (Real.pi / 2)..Real.pi, g θ := by
            simpa [I] using hsplit.symm
    _ = I + I := by
          rw [hsymm]
    _ = 2 * I := by
          ring
    _ ≤ 2 * (Real.pi / 2) := hIbound
    _ = Real.pi := by ring

/-- Helper for Lemma 3: the norm of the arc integrand factors into the norm of `f` times the
scalar damping kernel `exp (-r sin θ) * r`. -/
lemma norm_sectorArc_exp_integrand
    {f : ℂ → ℂ} {r θ : ℝ} (hr : 0 ≤ r) :
    ‖Complex.I * circleMap 0 r θ *
        (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ))‖ =
      ‖f (circleMap 0 r θ)‖ * (Real.exp (-r * Real.sin θ) * r) := by
  -- Rewrite the complex norm multiplicatively and expose the imaginary part of `circleMap`.
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    circleMap_zero_im, norm_circleMap_zero, abs_of_nonneg hr]
  ring

/-- Helper for Lemma 3: the damping integral over a subinterval of `[0, π]` is bounded by the
full upper-semicircle damping integral. -/
theorem intervalIntegral_exp_neg_sin_mul_le_of_subinterval
    {r θ₁ θ₂ : ℝ} (hr : 0 ≤ r) (hθ₁ : 0 ≤ θ₁) (hθ : θ₁ ≤ θ₂) (hθ₂ : θ₂ ≤ Real.pi) :
    ∫ θ in θ₁..θ₂, Real.exp (-r * Real.sin θ) * r ≤
      ∫ θ in (0 : ℝ)..Real.pi, Real.exp (-r * Real.sin θ) * r := by
  let g : ℝ → ℝ := fun θ ↦ Real.exp (-r * Real.sin θ) * r
  have hg_int : IntervalIntegrable g MeasureTheory.volume 0 Real.pi := by
    -- The damping kernel is continuous on the whole semicircle.
    have hg_cont : Continuous g := by
      fun_prop
    exact hg_cont.intervalIntegrable _ _
  have hg_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) Real.pi)] g := by
    filter_upwards with θ
    exact mul_nonneg (Real.exp_nonneg _) hr
  -- Monotonicity on nested intervals compares the subsector with the whole semicircle.
  simpa [g] using
    (intervalIntegral.integral_mono_interval (μ := MeasureTheory.volume) (f := g)
      hθ₁ hθ hθ₂ hg_nonneg hg_int)

/-- Lemma 3: if `f (r e^{iθ})` tends uniformly to `0` for `θ` in a sector of the upper
half-plane as `r → +∞`, then the contour integral of `f(z) * exp (I * z)` over the radius-`r`
arc in that sector tends to `0`, provided the defining arc integrand is eventually
interval-integrable. -/
theorem sectorArcIntegral_mul_exp_tendsto_zero
    (f : ℂ → ℂ) (θ₁ θ₂ : ℝ)
    (hθ₁ : 0 ≤ θ₁) (hθ : θ₁ ≤ θ₂) (hθ₂ : θ₂ ≤ Real.pi)
    (hint :
      ∀ᶠ r : ℝ in Filter.atTop,
        IntervalIntegrable
          (fun θ : ℝ ↦
            Complex.I * circleMap 0 r θ *
              (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ)))
          MeasureTheory.volume
          θ₁
          θ₂)
    (hlim :
      TendstoUniformlyOn
        (fun (r : ℝ) θ ↦ f (circleMap 0 r θ))
        0
        Filter.atTop
        (Set.Icc θ₁ θ₂)) :
    Filter.Tendsto
      (fun r : ℝ ↦ sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r θ₁ θ₂)
      Filter.atTop
      (nhds 0) := by
  rw [Metric.tendstoUniformlyOn_iff] at hlim
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hsmall :
      ∀ᶠ r : ℝ in Filter.atTop,
        ∀ θ ∈ Set.Icc θ₁ θ₂, ‖f (circleMap 0 r θ)‖ < ε / (2 * Real.pi) := by
    -- Uniform convergence turns into a uniform norm bound on the arc.
    have hε' : 0 < ε / (2 * Real.pi) := by
      positivity
    simpa [dist_eq_norm] using hlim (ε / (2 * Real.pi)) hε'
  filter_upwards [hsmall, Filter.eventually_ge_atTop (0 : ℝ), hint] with r hsmall_r hr hInt
  have hbound_int :
      IntervalIntegrable
        (fun θ : ℝ ↦ (ε / (2 * Real.pi)) * (Real.exp (-r * Real.sin θ) * r))
        MeasureTheory.volume
        θ₁
        θ₂ := by
    -- The scalar comparison kernel is continuous on the fixed angle interval.
    have hbound_cont :
        Continuous
          (fun θ : ℝ ↦ (ε / (2 * Real.pi)) * (Real.exp (-r * Real.sin θ) * r)) := by
      fun_prop
    exact hbound_cont.intervalIntegrable _ _
  have hnorm_lt :
      ‖sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r θ₁ θ₂‖ < ε := by
    -- Rewrite the contour integral and bound it by the scalar Jordan kernel.
    rw [sectorArcIntegral_def]
    calc
      ‖∫ θ in θ₁..θ₂,
          Complex.I * circleMap 0 r θ *
            (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ))‖
          ≤ ∫ θ in θ₁..θ₂,
              ‖Complex.I * circleMap 0 r θ *
                (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ))‖ := by
              exact intervalIntegral.norm_integral_le_integral_norm hθ
      _ ≤ ∫ θ in θ₁..θ₂,
            (ε / (2 * Real.pi)) * (Real.exp (-r * Real.sin θ) * r) := by
            refine intervalIntegral.integral_mono_on hθ hInt.norm hbound_int ?_
            intro θ hθ_mem
            have hsmall_θ :
                ‖f (circleMap 0 r θ)‖ ≤ ε / (2 * Real.pi) := by
              exact (hsmall_r θ hθ_mem).le
            rw [norm_sectorArc_exp_integrand hr]
            exact mul_le_mul_of_nonneg_right hsmall_θ
              (mul_nonneg (Real.exp_nonneg _) hr)
      _ = (ε / (2 * Real.pi)) *
            ∫ θ in θ₁..θ₂, Real.exp (-r * Real.sin θ) * r := by
            rw [intervalIntegral.integral_const_mul]
      _ ≤ (ε / (2 * Real.pi)) * Real.pi := by
            refine mul_le_mul_of_nonneg_left ?_ ?_
            · exact
                (intervalIntegral_exp_neg_sin_mul_le_of_subinterval hr hθ₁ hθ hθ₂).trans
                  (exp_neg_sin_mul_intervalIntegral_le_pi hr)
            · positivity
      _ = ε / 2 := by
            field_simp [Real.pi_ne_zero]
      _ < ε := by
            linarith
  simpa [dist_eq_norm] using hnorm_lt
