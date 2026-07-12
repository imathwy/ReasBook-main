import Mathlib

open Complex MeasureTheory
open scoped MeasureTheory Real Manifold

section

variable {f : ℂ → ℂ} {R : ℝ}
variable (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))

/-- Helper for Exercise 2: the real Jacobian determinant of complex multiplication by `a` is
`‖a‖²`. -/
lemma complex_abs_det_smul_id_eq_sq_norm (a : ℂ) :
    |((a • (1 : ℂ →L[ℝ] ℂ)).det)| = ‖a‖ ^ 2 := by
  -- Rewrite the continuous linear map as the algebra left-multiplication map on `ℂ`.
  have hmul :
      a • (1 : ℂ →L[ℝ] ℂ) = LinearMap.toContinuousLinearMap (Algebra.lmul ℝ ℂ a) := by
    ext z
    rfl
  calc
    |((a • (1 : ℂ →L[ℝ] ℂ)).det)| =
        |(LinearMap.toContinuousLinearMap (Algebra.lmul ℝ ℂ a)).det| := by
          rw [hmul]
    _ = |LinearMap.det (Algebra.lmul ℝ ℂ a)| := by
          rw [LinearMap.det_toContinuousLinearMap]
    _ = |Algebra.norm ℝ a| := by
      rw [Algebra.norm_eq_matrix_det Complex.basisOneI, Algebra.leftMulMatrix_apply,
        ← LinearMap.det_toMatrix Complex.basisOneI]
    _ = ‖a‖ ^ 2 := by
      rw [Algebra.norm_complex_apply, _root_.abs_of_nonneg (Complex.normSq_nonneg a),
        Complex.normSq_eq_norm_sq]

/-- Helper for Exercise 2: on the polar target, membership in the closed disc `|z| ≤ R` is exactly
the radial inequality `r ≤ R`. -/
lemma mem_closedBall_polarCoord_symm_iff
    {p : ℝ × ℝ} (hp : p ∈ Complex.polarCoord.target) :
    Complex.polarCoord.symm p ∈ Metric.closedBall (0 : ℂ) R ↔ p.1 ≤ R := by
  -- On the target we have `p.1 > 0`, so `‖polarCoord.symm p‖ = p.1`.
  rcases hp with ⟨hp0, hpθ⟩
  have hp0' : 0 < p.1 := by simpa using hp0
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Complex.norm_polarCoord_symm, abs_of_pos hp0']

/-- Helper for Exercise 2: the disc energy integral admits the expected polar-coordinate rewrite on
`(0, R] × (-π, π)`. -/
lemma closedBall_integral_sq_norm_deriv_eq_polar
    (hR : 0 ≤ R) :
    ∫ z in Metric.closedBall (0 : ℂ) R, ‖deriv f z‖ ^ 2 ∂volume =
      ∫ p in (Set.Ioc (0 : ℝ) R) ×ˢ Set.Ioo (-π) π,
        p.1 * ‖deriv f (Complex.polarCoord.symm p)‖ ^ 2 := by
  let g : ℂ → ℝ :=
    (Metric.closedBall (0 : ℂ) R).indicator (fun z : ℂ ↦ ‖deriv f z‖ ^ 2)
  have hprod :
      MeasurableSet ((Set.Ioc (0 : ℝ) R) ×ˢ Set.Ioo (-π) π) :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have hsubset :
      ((Set.Ioc (0 : ℝ) R) ×ˢ Set.Ioo (-π) π) ⊆ Complex.polarCoord.target := by
    intro p hp
    exact ⟨hp.1.1, hp.2⟩
  -- Apply the polar change of variables to the disc indicator.
  calc
    ∫ z in Metric.closedBall (0 : ℂ) R, ‖deriv f z‖ ^ 2 ∂volume = ∫ z, g z := by
      simpa [g] using
        (integral_indicator (μ := volume)
          (f := fun z : ℂ ↦ ‖deriv f z‖ ^ 2) measurableSet_closedBall).symm
    _ = ∫ p in Complex.polarCoord.target, p.1 * g (Complex.polarCoord.symm p) := by
      simpa [g, smul_eq_mul] using (Complex.integral_comp_polarCoord_symm g).symm
    _ = ∫ p in Complex.polarCoord.target,
          ((Set.Ioc (0 : ℝ) R) ×ˢ Set.Ioo (-π) π).indicator
            (fun p : ℝ × ℝ ↦ p.1 * ‖deriv f (Complex.polarCoord.symm p)‖ ^ 2) p := by
          refine setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet ?_
          intro p hp
          by_cases hpBall : Complex.polarCoord.symm p ∈ Metric.closedBall (0 : ℂ) R
          · have hpProd : p ∈ (Set.Ioc (0 : ℝ) R) ×ˢ Set.Ioo (-π) π := by
              rcases hp with ⟨hp0, hpθ⟩
              have hp0' : 0 < p.1 := by simpa using hp0
              exact ⟨⟨hp0', (mem_closedBall_polarCoord_symm_iff (R := R) ⟨hp0, hpθ⟩).1 hpBall⟩,
                hpθ⟩
            dsimp [g]
            rw [Set.indicator_of_mem hpBall, Set.indicator_of_mem hpProd]
          · have hpProd : p ∉ (Set.Ioc (0 : ℝ) R) ×ˢ Set.Ioo (-π) π := by
              intro hpProd
              exact hpBall <|
                (mem_closedBall_polarCoord_symm_iff (R := R) (hsubset hpProd)).2 hpProd.1.2
            dsimp [g]
            rw [Set.indicator_of_notMem hpBall, Set.indicator_of_notMem hpProd]
            ring
    _ = ∫ p in Complex.polarCoord.target ∩ ((Set.Ioc (0 : ℝ) R) ×ˢ Set.Ioo (-π) π),
          p.1 * ‖deriv f (Complex.polarCoord.symm p)‖ ^ 2 := by
            rw [setIntegral_indicator hprod]
    _ = ∫ p in (Set.Ioc (0 : ℝ) R) ×ˢ Set.Ioo (-π) π,
          p.1 * ‖deriv f (Complex.polarCoord.symm p)‖ ^ 2 := by
            rw [Set.inter_eq_right.mpr hsubset]

include hf

/-- Helper for Exercise 2: for every radius `r ≤ R`, the square of `‖f'(0)‖` is bounded by the
circle-average of `‖f'‖²` on the circle of radius `r`. -/
lemma sq_norm_deriv_zero_le_circle_average_sq_norm_deriv
    {r : ℝ} (hr0 : 0 ≤ r) (hrR : r ≤ R) :
    ‖deriv f 0‖ ^ 2 ≤
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2 := by
  have hderivAnalytic : AnalyticOnNhd ℂ (deriv f) (Metric.closedBall (0 : ℂ) R) := by
    simpa using
      (AnalyticOnNhd.deriv (𝕜 := ℂ) (F := ℂ) (f := f) (s := Metric.closedBall (0 : ℂ) R) hf)
  have hderivDiffCont : DiffContOnCl ℂ (deriv f) (Metric.ball (0 : ℂ) r) := by
    -- Restrict the mean-value theorem for `deriv f` from the disc of radius `R` to radius `r`.
    simpa [abs_of_nonneg hr0] using
      (hderivAnalytic.differentiableOn.diffContOnCl_ball (c := (0 : ℂ)) (R := r)
        (Metric.closedBall_subset_closedBall hrR))
  have hderivDiffContAbs : DiffContOnCl ℂ (deriv f) (Metric.ball (0 : ℂ) |r|) := by
    simpa [abs_of_nonneg hr0] using hderivDiffCont
  have hmean : Real.circleAverage (deriv f) 0 r = deriv f 0 := by
    -- The holomorphic mean-value property identifies the circle average with the center value.
    simpa [abs_of_nonneg hr0] using hderivDiffContAbs.circleAverage
  let g : ℝ → ℝ := fun θ ↦ ‖deriv f (circleMap 0 r θ)‖
  have hcircle : Continuous (circleMap (0 : ℂ) r) := by
    fun_prop
  have hcontDeriv : Continuous fun θ : ℝ ↦ deriv f (circleMap 0 r θ) := by
    -- Compose the continuity of `deriv f` on the closed disc with the circular parametrization.
    rw [← continuousOn_univ]
    refine hderivAnalytic.continuousOn.comp hcircle.continuousOn ?_
    intro θ hθ
    exact Metric.closedBall_subset_closedBall hrR (circleMap_mem_closedBall 0 hr0 θ)
  have hcontG : Continuous g := by
    simpa [g] using hcontDeriv.norm
  let m : ℝ := (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), g θ
  have hnorm : ‖deriv f 0‖ ≤ m := by
    -- Take norms in the mean-value identity, then estimate the norm of the integral by the
    -- integral of the norm.
    calc
      ‖deriv f 0‖ = ‖(2 * π)⁻¹ • ∫ θ in (0 : ℝ)..(2 * π), deriv f (circleMap 0 r θ)‖ := by
        rw [← hmean, Real.circleAverage_def]
      _ = (2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..(2 * π), deriv f (circleMap 0 r θ)‖ := by
        have hnonneg : 0 ≤ (2 * π)⁻¹ := by
          positivity
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      _ ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), g θ := by
        exact mul_le_mul_of_nonneg_left
          (intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le)
          (by positivity)
      _ = m := by
        rfl
  have hcontGSq : Continuous fun θ : ℝ ↦ g θ ^ 2 := by
    simpa using hcontG.pow 2
  have hgInt : IntervalIntegrable g volume 0 (2 * π) := hcontG.intervalIntegrable _ _
  have hgSqInt : IntervalIntegrable (fun θ : ℝ ↦ g θ ^ 2) volume 0 (2 * π) :=
    hcontGSq.intervalIntegrable _ _
  have hleftInt : IntervalIntegrable (fun θ : ℝ ↦ 2 * (m * g θ)) volume 0 (2 * π) := by
    have hleftCont : Continuous fun θ : ℝ ↦ 2 * (m * g θ) :=
      continuous_const.mul (continuous_const.mul hcontG)
    exact hleftCont.intervalIntegrable _ _
  have hconstInt : IntervalIntegrable (fun _ : ℝ ↦ m ^ 2) volume 0 (2 * π) :=
    continuous_const.intervalIntegrable _ _
  have hrightInt : IntervalIntegrable (fun θ : ℝ ↦ m ^ 2 + g θ ^ 2) volume 0 (2 * π) := by
    have hrightCont : Continuous fun θ : ℝ ↦ m ^ 2 + g θ ^ 2 :=
      continuous_const.add hcontGSq
    exact hrightCont.intervalIntegrable _ _
  have hpointwise : ∀ θ : ℝ, 2 * (m * g θ) ≤ m ^ 2 + g θ ^ 2 := by
    intro θ
    nlinarith [two_mul_le_add_sq m (g θ)]
  have hsqAverage :
      m ^ 2 ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), g θ ^ 2 := by
    have hmono :
        ∫ θ in (0 : ℝ)..(2 * π), 2 * (m * g θ) ≤
          ∫ θ in (0 : ℝ)..(2 * π), (m ^ 2 + g θ ^ 2) := by
      -- Integrate the pointwise square estimate to obtain the one-variable square-average bound.
      exact intervalIntegral.integral_mono_on_of_le_Ioo Real.two_pi_pos.le hleftInt hrightInt
        (fun θ hθ ↦ hpointwise θ)
    have hm :
        ∫ θ in (0 : ℝ)..(2 * π), g θ = 2 * π * m := by
      simp [m]
      field_simp [Real.two_pi_pos.ne']
    have hcore :
        2 * π * m ^ 2 ≤ ∫ θ in (0 : ℝ)..(2 * π), g θ ^ 2 := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hconstInt hgSqInt,
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hm] at hmono
      ring_nf at hmono ⊢
      nlinarith [hmono, Real.two_pi_pos]
    calc
      m ^ 2 = (2 * π)⁻¹ * (2 * π * m ^ 2) := by
        field_simp [Real.two_pi_pos.ne']
      _ ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), g θ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hcore (by positivity)
  have hnormSq : ‖deriv f 0‖ ^ 2 ≤ m ^ 2 := by
    nlinarith [hnorm, norm_nonneg (deriv f 0)]
  -- Combine the norm-average estimate with the one-variable square-average bound.
  calc
    ‖deriv f 0‖ ^ 2 ≤ m ^ 2 := hnormSq
    _ ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), g θ ^ 2 := hsqAverage
    _ = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2 := by
      rfl

/-- Helper for Exercise 2: the polar area integrand rewrites as the expected radius-angle
iterated integral over `0 ≤ r ≤ R` and `0 ≤ θ ≤ 2π`. -/
lemma polar_sq_norm_deriv_setIntegral_eq_radius_angleIntegral
    (hR : 0 ≤ R) :
    ∫ p in (Set.Ioc (0 : ℝ) R) ×ˢ Set.Ioo (-π) π,
      p.1 * ‖deriv f (Complex.polarCoord.symm p)‖ ^ 2 =
        ∫ r in (0 : ℝ)..R,
          r * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2 := by
  let g : ℝ × ℝ → ℝ := fun p ↦ p.1 * ‖deriv f (circleMap 0 p.1 p.2)‖ ^ 2
  have hderivAnalytic : AnalyticOnNhd ℂ (deriv f) (Metric.closedBall (0 : ℂ) R) := by
    simpa using
      (AnalyticOnNhd.deriv (𝕜 := ℂ) (F := ℂ) (f := f) (s := Metric.closedBall (0 : ℂ) R) hf)
  have hcontDeriv : ContinuousOn (deriv f) (Metric.closedBall (0 : ℂ) R) :=
    hderivAnalytic.continuousOn
  have hcontG : ContinuousOn g (Set.Icc (0 : ℝ) R ×ˢ Set.Icc (-π) π) := by
    -- The polar integrand is continuous on the compact closed box `0 ≤ r ≤ R`, `-π ≤ θ ≤ π`.
    refine continuous_fst.continuousOn.mul ?_
    have hcircle : Continuous fun p : ℝ × ℝ ↦ circleMap 0 p.1 p.2 := by
      fun_prop
    refine ((hcontDeriv.comp hcircle.continuousOn) ?_).norm.pow 2
    intro p hp
    exact Metric.closedBall_subset_closedBall hp.1.2 (circleMap_mem_closedBall 0 hp.1.1 p.2)
  have hint :
      IntegrableOn g ((Set.Ioc (0 : ℝ) R) ×ˢ Set.Ioo (-π) π) := by
    -- The compact-box continuity gives integrability, and the open box is a subset of that box.
    refine (hcontG.integrableOn_compact ?_).mono_set ?_
    · exact (isCompact_Icc.prod isCompact_Icc)
    · intro p hp
      exact ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have hintProd :
      IntegrableOn g ((Set.Ioc (0 : ℝ) R) ×ˢ Set.Ioo (-π) π) (volume.prod volume) := by
    simpa [Measure.volume_eq_prod] using hint
  calc
    ∫ p in (Set.Ioc (0 : ℝ) R) ×ˢ Set.Ioo (-π) π,
        p.1 * ‖deriv f (Complex.polarCoord.symm p)‖ ^ 2 =
      ∫ p in (Set.Ioc (0 : ℝ) R) ×ˢ Set.Ioo (-π) π, g p := by
        -- Rewrite `polarCoord.symm` as the usual circle parametrization pointwise.
        refine setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioo) ?_
        intro p hp
        simpa [g, Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I]
    _ = ∫ r in Set.Ioc (0 : ℝ) R, ∫ θ in Set.Ioo (-π) π, g (r, θ) := by
          simpa [Measure.volume_eq_prod] using
            (MeasureTheory.setIntegral_prod (μ := volume) (ν := volume) g hintProd)
    _ = ∫ r in Set.Ioc (0 : ℝ) R,
          r * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2 := by
            -- Shift the angular integral from `(-π, π)` to `(0, 2π)` using periodicity.
            refine setIntegral_congr_fun measurableSet_Ioc ?_
            intro r hr
            have hperiodic :
                Function.Periodic (fun θ : ℝ ↦ ‖deriv f (circleMap 0 r θ)‖ ^ 2) (2 * π) := by
              intro θ
              simp [periodic_circleMap 0 r θ]
            have hangle :
                ∫ θ in Set.Ioo (-π) π, ‖deriv f (circleMap 0 r θ)‖ ^ 2 =
                  ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2 := by
              calc
                ∫ θ in Set.Ioo (-π) π, ‖deriv f (circleMap 0 r θ)‖ ^ 2 =
                    ∫ θ in Set.Ioc (-π) π, ‖deriv f (circleMap 0 r θ)‖ ^ 2 := by
                      rw [← integral_Ioc_eq_integral_Ioo]
                _ = ∫ θ in (-π : ℝ)..π, ‖deriv f (circleMap 0 r θ)‖ ^ 2 := by
                      rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
                _ = ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2 := by
                      convert hperiodic.intervalIntegral_add_eq (-π) 0 using 1 <;> ring
            change ∫ θ in Set.Ioo (-π) π, r * ‖deriv f (circleMap 0 r θ)‖ ^ 2 =
              r * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2
            rw [integral_const_mul]
            rw [hangle]
    _ = ∫ r in (0 : ℝ)..R,
          r * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2 := by
            rw [← intervalIntegral.integral_of_le hR]

end
