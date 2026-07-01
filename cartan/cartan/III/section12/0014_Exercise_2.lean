import Mathlib

-- Semantic search tool `lean_leansearch` was unavailable in this environment; notation was
-- verified locally against mathlib and nearby repository precedent. The holomorphic-neighborhood
-- owner for this file was checked against `AnalyticOnNhd`, `circleMap`, and Euclidean Hausdorff
-- measure on the complex plane.

-- Declarations for this item will be appended below by the statement pipeline.

open Complex MeasureTheory
open scoped MeasureTheory Real Manifold

section

variable {f : ℂ → ℂ} {R : ℝ}
variable (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))

/-- Helper for Exercise 2: the boundary parametrization `θ ↦ f (circleMap 0 R θ)` has speed
`R * ‖f'(circleMap 0 R θ)‖`. -/
lemma boundary_circle_param_speed
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (hR : 0 ≤ R) (θ : ℝ) :
    ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖ =
      R * ‖deriv f (circleMap 0 R θ)‖ := by
  -- The chain rule identifies the derivative of the boundary parametrization.
  have hderiv :
      HasDerivAt (fun t : ℝ ↦ f (circleMap 0 R t))
        (deriv (circleMap 0 R) θ * deriv f (circleMap 0 R θ)) θ := by
    simpa [Function.comp] using
      ((hf (circleMap 0 R θ) (circleMap_mem_closedBall 0 hR θ)).differentiableAt.hasDerivAt).scomp
        θ (hasDerivAt_circleMap 0 R θ)
  -- The norm of `circleMap 0 R θ * I` is exactly `R`.
  calc
    ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖ =
        ‖deriv (circleMap 0 R) θ * deriv f (circleMap 0 R θ)‖ := by
          rw [hderiv.deriv]
    _ = ‖deriv (circleMap 0 R) θ‖ * ‖deriv f (circleMap 0 R θ)‖ := norm_mul _ _
    _ = R * ‖deriv f (circleMap 0 R θ)‖ := by
          simp [deriv_circleMap, norm_circleMap_zero, abs_of_nonneg hR]

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

/-- Helper for Exercise 2: the boundary image can be rewritten using the standard angular
parametrization on `Set.Ioc (0 : ℝ) (2 * π)`. -/
lemma boundary_image_eq_circle_param_image
    (hR : 0 ≤ R) :
    f '' Metric.sphere (0 : ℂ) R =
      (fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π) := by
  -- Rewrite the geometric circle as the image of `circleMap`, then push forward by `f`.
  have hsphere :
      circleMap (0 : ℂ) R '' Set.Ioc (0 : ℝ) (2 * π) = Metric.sphere (0 : ℂ) R := by
    simpa [abs_of_nonneg hR] using image_circleMap_Ioc (0 : ℂ) R
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← hsphere] at hz
    rcases hz with ⟨θ, hθ, rfl⟩
    exact ⟨θ, hθ, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨circleMap 0 R θ, ?_, rfl⟩
    simpa [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R θ

/-- Helper for Exercise 2: injectivity of `f` on the geometric boundary transfers to injectivity of
the angular boundary parametrization on `Set.Ioc (0 : ℝ) (2 * π)` when `R ≠ 0`. -/
lemma boundary_circle_param_injOn
    (hR : 0 ≤ R) (hR0 : R ≠ 0)
    (hinj : Set.InjOn f (Metric.sphere (0 : ℂ) R)) :
    Set.InjOn (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Ioc (0 : ℝ) (2 * π)) := by
  -- First use the geometric injectivity of `f` to identify boundary points, then use the strict
  -- bound `|θ - φ| < 2π` to recover equality of the angles from the `circleMap` equality.
  intro θ hθ φ hφ hEq
  have hcircleEq : circleMap 0 R θ = circleMap 0 R φ := by
    apply hinj
    · simpa [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R θ
    · simpa [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R φ
    · exact hEq
  apply eq_of_circleMap_eq hR0
  · rw [abs_lt]
    constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2, Real.two_pi_pos]
  · exact hcircleEq

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

/-- Helper for Exercise 2: the angular boundary parametrization is `C¹` on
`[0, 2 π]`. -/
lemma boundary_circle_param_contDiffOn
    (hR : 0 ≤ R) :
    ContDiffOn ℝ 1 (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Icc (0 : ℝ) (2 * π)) := by
  -- Restrict the analytic regularity of `f` to real scalars and compose with the smooth circle
  -- map.
  have hfcontComplex : ContDiffOn ℂ 1 f (Metric.closedBall (0 : ℂ) R) :=
    hf.contDiffOn_of_completeSpace
  have hfcont : ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R) :=
    hfcontComplex.restrict_scalars ℝ
  exact hfcont.comp (contDiff_circleMap 0 R).contDiffOn fun θ hθ ↦
    circleMap_mem_closedBall 0 hR θ

/-- Helper for Exercise 2: the angular boundary parametrization closes after one full turn. -/
lemma boundary_circle_param_endpoint_eq :
    (fun θ : ℝ ↦ f (circleMap 0 R θ)) (0 : ℝ) =
      (fun θ : ℝ ↦ f (circleMap 0 R θ)) (2 * π) := by
  -- `circleMap` returns to the starting point at angle `2π`.
  simp [circleMap_zero, Complex.exp_two_pi_mul_I]

/-- Helper for Exercise 2: integrating the boundary speed of the angular parametrization gives the
textbook factor `R * ∫ ‖f'(circleMap 0 R θ)‖`. -/
lemma boundary_circle_param_integral_speed_eq
    (hR : 0 ≤ R) :
    ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖ =
      R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖ := by
  -- Integrate the pointwise speed formula from `boundary_circle_param_speed`.
  calc
    ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖ =
        ∫ θ in (0 : ℝ)..(2 * π), R * ‖deriv f (circleMap 0 R θ)‖ := by
          apply intervalIntegral.integral_congr_ae_restrict
            (a := (0 : ℝ)) (b := 2 * π) (μ := volume)
            (f := fun θ : ℝ ↦ ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖)
            (g := fun θ : ℝ ↦ R * ‖deriv f (circleMap 0 R θ)‖)
          exact Filter.Eventually.of_forall fun θ ↦
            boundary_circle_param_speed (hf := hf) hR θ
    _ = R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖ := by
          rw [intervalIntegral.integral_const_mul]

/-- Helper for Exercise 2: a preconnected set in a metric space has Hausdorff `1`-measure at least
the distance between any two of its points. -/
lemma hausdorffMeasure_ge_dist_of_isPreconnected
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hs : IsPreconnected s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ENNReal.ofReal (dist x y) ≤ μH[1] s := by
  let g : E → ℝ := dist x
  have hLip : LipschitzWith 1 g := LipschitzWith.dist_right x
  have hpre : IsPreconnected (g '' s) := hs.image g hLip.continuous.continuousOn
  have hsubset : Set.Icc 0 (dist x y) ⊆ g '' s := by
    -- The distance image is a preconnected subset of `ℝ` containing the endpoint distances.
    refine hpre.Icc_subset ?_ ?_
    · exact ⟨x, hx, by simp [g]⟩
    · exact ⟨y, hy, by simp [g]⟩
  -- Compare the image with the interval of distances, then use the Lipschitz upper bound.
  calc
    ENNReal.ofReal (dist x y) = μH[1] (Set.Icc 0 (dist x y)) := by
      rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]
      simp
    _ ≤ μH[1] (g '' s) := measure_mono hsubset
    _ ≤ μH[1] s := by
      simpa using hLip.hausdorffMeasure_image_le (d := (1 : ℝ)) (by norm_num) s

/-
The next geometric interval-image lemmas are independent of the holomorphic data `hf`.
-/
omit hf

/-- Helper for Exercise 2: in dimension `1`, Euclidean Hausdorff measure coincides with ordinary
Hausdorff measure. -/
lemma euclideanHausdorffMeasure_one_eq_hausdorffMeasure_one
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] :
    (μHE[1] : Measure X) = (μH[1] : Measure X) := by
  -- TODO: identify the Euclidean normalization scalar in dimension `1` with `1` by evaluating
  -- `μHE[1]` and `μH[1]` on a one-dimensional Euclidean model interval. This normalization bridge
  -- is now isolated from the remaining curve-length arguments.
  sorry

/-- Helper for Exercise 2: adjoining closed interval images concatenate exactly. -/
lemma image_Icc_union_image_Icc_eq_image_Icc
    {γ : ℝ → ℂ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    γ '' Set.Icc a b ∪ γ '' Set.Icc b c = γ '' Set.Icc a c := by
  -- Push the standard interval union identity through the map `γ`.
  rw [← Set.image_union]
  congr 1
  exact Set.Icc_union_Icc_eq_Icc hab hbc

/-- Helper for Exercise 2: if `γ` is injective on a larger closed interval, then the images of two
adjacent subintervals meet only at the shared endpoint. -/
lemma image_Icc_inter_image_Icc_subset_shared_endpoint
    {γ : ℝ → ℂ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hinj : Set.InjOn γ (Set.Icc a c)) :
    (γ '' Set.Icc a b) ∩ (γ '' Set.Icc b c) ⊆ {γ b} := by
  intro z hz
  rcases hz with ⟨hzLeft, hzRight⟩
  rcases hzLeft with ⟨x, hx, rfl⟩
  rcases hzRight with ⟨y, hy, hxy⟩
  have hx' : x ∈ Set.Icc a c := ⟨hx.1, hx.2.trans hbc⟩
  have hy' : y ∈ Set.Icc a c := ⟨hab.trans hy.1, hy.2⟩
  have hxy' : x = y := hinj hx' hy' hxy.symm
  have hxb : x = b := by
    refine le_antisymm ?_ ?_
    · exact hx.2
    · simpa [hxy'] using hy.1
  simpa [hxb]

/-- Helper for Exercise 2: adjacent subinterval images of an injective curve have zero Euclidean
Hausdorff `1`-measure overlap. -/
lemma image_Icc_adjacent_overlap_measure_zero_of_injOn
    {γ : ℝ → ℂ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hinj : Set.InjOn γ (Set.Icc a c)) :
    μHE[1] ((γ '' Set.Icc a b) ∩ (γ '' Set.Icc b c)) = 0 := by
  -- Reduce the overlap to the singleton shared endpoint and use that Hausdorff measure has no
  -- atoms in dimension `1`.
  have hsubset :
      (γ '' Set.Icc a b) ∩ (γ '' Set.Icc b c) ⊆ {γ b} :=
    image_Icc_inter_image_Icc_subset_shared_endpoint hab hbc hinj
  haveI := MeasureTheory.Measure.noAtoms_hausdorff ℂ (show 0 < (1 : ℝ) by norm_num)
  have hzero : μHE[1] ({γ b} : Set ℂ) = 0 := by
    -- Normalize Euclidean Hausdorff `1`-measure to ordinary Hausdorff measure, then use
    -- atom-freeness.
    rw [euclideanHausdorffMeasure_one_eq_hausdorffMeasure_one]
    simp
  exact le_antisymm ((measure_mono hsubset).trans hzero.le) (by simp)

/-- Helper for Exercise 2: for an injective continuous curve, the Euclidean Hausdorff
`1`-measure of the image of a concatenated interval is the sum of the measures of the adjacent
subarc images. -/
lemma image_Icc_union_measure_eq_of_injOn
    {γ : ℝ → ℂ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcont : ContinuousOn γ (Set.Icc a c)) (hinj : Set.InjOn γ (Set.Icc a c)) :
    μHE[1] (γ '' Set.Icc a c) =
      μHE[1] (γ '' Set.Icc a b) + μHE[1] (γ '' Set.Icc b c) := by
  have hleftCont : ContinuousOn γ (Set.Icc a b) := by
    -- Restrict continuity from the large interval to the left subinterval.
    refine hcont.mono ?_
    intro x hx
    exact ⟨hx.1, hx.2.trans hbc⟩
  have hrightCont : ContinuousOn γ (Set.Icc b c) := by
    -- Restrict continuity from the large interval to the right subinterval.
    refine hcont.mono ?_
    intro x hx
    exact ⟨hab.trans hx.1, hx.2⟩
  have hleftMeas : MeasurableSet (γ '' Set.Icc a b) := by
    -- Continuous images of compact intervals are compact, hence measurable.
    exact (isCompact_Icc.image_of_continuousOn hleftCont).measurableSet
  have hrightMeas : MeasurableSet (γ '' Set.Icc b c) := by
    -- The same compact-image argument handles the right subinterval.
    exact (isCompact_Icc.image_of_continuousOn hrightCont).measurableSet
  have hunion :
      μHE[1] ((γ '' Set.Icc a b) ∪ (γ '' Set.Icc b c)) +
          μHE[1] ((γ '' Set.Icc a b) ∩ (γ '' Set.Icc b c)) =
        μHE[1] (γ '' Set.Icc a b) + μHE[1] (γ '' Set.Icc b c) := by
    simpa using
      (measure_union_add_inter (μ := (μHE[1] : Measure ℂ))
        (γ '' Set.Icc a b) hrightMeas)
  -- Rewrite the union as the full interval image, then collapse the overlap term to zero.
  simpa [image_Icc_union_image_Icc_eq_image_Icc hab hbc,
    image_Icc_adjacent_overlap_measure_zero_of_injOn hab hbc hinj] using hunion

include hf

/-- Helper for Exercise 2: injectivity on the circle transfers to injectivity on each closed
half-arc of the angular parametrization. -/
lemma boundary_circle_param_half_injOn
    (hR : 0 ≤ R) (hR0 : R ≠ 0)
    (hinj : Set.InjOn f (Metric.sphere (0 : ℂ) R)) :
    Set.InjOn (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Icc (0 : ℝ) π) ∧
      Set.InjOn (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Icc π (2 * π)) := by
  constructor
  · intro θ hθ φ hφ hEq
    have hcircleEq : circleMap 0 R θ = circleMap 0 R φ := by
      apply hinj
      · simpa [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R θ
      · simpa [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R φ
      · exact hEq
    -- On `[0, π]` the angular difference is automatically strictly smaller than `2π`.
    apply eq_of_circleMap_eq hR0
    · rw [abs_lt]
      constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2, Real.pi_pos, Real.two_pi_pos]
    · exact hcircleEq
  · intro θ hθ φ hφ hEq
    have hcircleEq : circleMap 0 R θ = circleMap 0 R φ := by
      apply hinj
      · simpa [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R θ
      · simpa [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R φ
      · exact hEq
    -- The same argument works on `[π, 2π]`, where the difference lies in `[-π, π]`.
    apply eq_of_circleMap_eq hR0
    · rw [abs_lt]
      constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2, Real.pi_pos, Real.two_pi_pos]
    · exact hcircleEq

/-- Helper for Exercise 2: the two closed half-arc images intersect only at the two global
endpoints, so their overlap has Hausdorff `1`-measure zero. -/
lemma boundary_circle_half_image_overlap_measure_zero
    (hR : 0 ≤ R) (hR0 : R ≠ 0)
    (hinj : Set.InjOn f (Metric.sphere (0 : ℂ) R)) :
    μHE[1]
        (((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) ∩
          ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π))) = 0 := by
  let γ : ℝ → ℂ := fun θ ↦ f (circleMap 0 R θ)
  have hsubset :
      (γ '' Set.Icc (0 : ℝ) π) ∩ (γ '' Set.Icc π (2 * π)) ⊆ {γ 0, γ π} := by
    intro z hz
    rcases hz with ⟨⟨θ, hθ, rfl⟩, φ, hφ, hEq⟩
    have hcircleEq : circleMap 0 R θ = circleMap 0 R φ := by
      apply hinj
      · simpa [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R θ
      · simpa [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R φ
      · exact hEq.symm
    by_cases hendpoint : θ = 0 ∧ φ = 2 * π
    · rcases hendpoint with ⟨rfl, rfl⟩
      simp [γ, boundary_circle_param_endpoint_eq (hf := hf)]
    · have hθleφ : θ ≤ φ := hθ.2.trans hφ.1
      have hθφ_nonneg : 0 ≤ φ - θ := sub_nonneg.mpr hθleφ
      have hθφ_le : φ - θ ≤ 2 * π := by
        nlinarith [hφ.2, hθ.1]
      have habs : |θ - φ| = φ - θ := by
        rw [abs_of_nonpos]
        · ring
        · exact sub_nonpos.mpr hθleφ
      have hneqTop : φ - θ ≠ 2 * π := by
        intro htop
        have hθ0 : θ = 0 := by
          linarith [hφ.2, hθ.1, htop]
        have hφTop : φ = 2 * π := by
          linarith [htop, hθ0]
        exact hendpoint ⟨hθ0, hφTop⟩
      have hdist : |θ - φ| < 2 * π := by
        rw [habs]
        exact lt_of_le_of_ne hθφ_le hneqTop
      have hθφ : θ = φ := eq_of_circleMap_eq hR0 hdist hcircleEq
      have hπ : θ = π := by linarith [hθ.2, hφ.1, hθφ]
      simp [γ, hπ]
  haveI := MeasureTheory.Measure.noAtoms_hausdorff ℂ (show 0 < (1 : ℝ) by norm_num)
  have hzeroHaus : (μH[1] : Measure ℂ) ({γ 0, γ π} : Set ℂ) = 0 := by
    simpa using (Finset.measure_zero ({γ 0, γ π} : Finset ℂ) (μ := μH[1]))
  have hzeroSet : μHE[1] ({γ 0, γ π} : Set ℂ) = 0 := by
    -- The two-dimensional ambient space still uses the same `1`-dimensional normalization.
    rw [euclideanHausdorffMeasure_one_eq_hausdorffMeasure_one]
    exact hzeroHaus
  exact le_antisymm ((measure_mono hsubset).trans hzeroSet.le) (by simp)

/-- Helper for Exercise 2: the open-closed full-turn image is exactly the union of the two closed
half-arc images. -/
lemma boundary_circle_param_image_eq_half_union :
    (fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π) =
      ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) ∪
        ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π)) := by
  let γ : ℝ → ℂ := fun θ ↦ f (circleMap 0 R θ)
  -- Split the angular parameter domain at `π`, using the endpoint identification at `0` and `2π`.
  ext z
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    by_cases hθπ : θ ≤ π
    · exact Or.inl ⟨θ, ⟨hθ.1.le, hθπ⟩, rfl⟩
    · exact Or.inr ⟨θ, ⟨le_of_not_ge hθπ, hθ.2⟩, rfl⟩
  · rintro (⟨θ, hθ, rfl⟩ | ⟨θ, hθ, rfl⟩)
    · by_cases hθ0 : θ = 0
      · -- The missing left endpoint is recovered from the right endpoint `2π`.
        refine ⟨2 * π, ⟨by positivity, le_rfl⟩, ?_⟩
        simpa [γ, hθ0] using (boundary_circle_param_endpoint_eq (hf := hf) (f := f) (R := R)).symm
      · refine ⟨θ, ⟨lt_of_le_of_ne hθ.1 (by simpa [eq_comm] using hθ0), ?_⟩, rfl⟩
        linarith [hθ.2, Real.pi_pos]
    · refine ⟨θ, ⟨?_, hθ.2⟩, rfl⟩
      linarith [hθ.1, Real.pi_pos]

/-- Helper for Exercise 2: after the midpoint split, the Hausdorff `1`-measure of the full boundary
image is the sum of the two half-image measures because the overlap has measure zero. -/
lemma boundary_circle_param_half_union_measure_eq
    (hR : 0 ≤ R)
    (hhalfOverlap :
      μHE[1]
          (((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) ∩
            ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π))) = 0) :
    μHE[1]
        (((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) ∪
          ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π))) =
      μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) +
        μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π)) := by
  let γ : ℝ → ℂ := fun θ ↦ f (circleMap 0 R θ)
  have hcont :
      ContDiffOn ℝ 1 γ (Set.Icc (0 : ℝ) (2 * π)) :=
    boundary_circle_param_contDiffOn (hf := hf) (f := f) (R := R) hR
  have hleftMeas : MeasurableSet (γ '' Set.Icc (0 : ℝ) π) := by
    -- Each half-image is compact because the parametrization is continuous on the closed interval.
    exact
      (isCompact_Icc.image_of_continuousOn
        (hcont.continuousOn.mono <| by
          intro θ hθ
          exact ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)).measurableSet
  have hrightMeas : MeasurableSet (γ '' Set.Icc π (2 * π)) := by
    -- The right half-image is handled by the same compact-image argument.
    exact
      (isCompact_Icc.image_of_continuousOn
        (hcont.continuousOn.mono <| by
          intro θ hθ
          exact ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)).measurableSet
  have hunion :
      μHE[1] ((γ '' Set.Icc (0 : ℝ) π) ∪ (γ '' Set.Icc π (2 * π))) +
          μHE[1] ((γ '' Set.Icc (0 : ℝ) π) ∩ (γ '' Set.Icc π (2 * π))) =
        μHE[1] (γ '' Set.Icc (0 : ℝ) π) + μHE[1] (γ '' Set.Icc π (2 * π)) := by
    simpa [γ] using
      (measure_union_add_inter (μ := (μHE[1] : Measure ℂ))
        (γ '' Set.Icc (0 : ℝ) π) hrightMeas)
  -- Collapse the intersection term using the already-proved zero-overlap fact.
  rw [hhalfOverlap, add_zero] at hunion
  exact hunion

/-- Helper for Exercise 2: on a single closed interval cell, if the interval derivative stays
`δ`-close to a fixed vector `v`, then the speed integral is bounded by the chord length plus the
expected oscillation error. -/
lemma single_cell_speed_le_chord_add_derivWithin_oscillation
    {γ : ℝ → ℂ} {x y δ : ℝ} {v : ℂ} (hxy : x ≤ y)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc x y))
    (hδ : ∀ t ∈ Set.Icc x y, ‖derivWithin γ (Set.Icc x y) t - v‖ ≤ δ) :
    ∫ t in x..y, ‖derivWithin γ (Set.Icc x y) t‖ ≤
      dist (γ x) (γ y) + 2 * δ * (y - x) := by
  by_cases hEq : x = y
  · -- On a degenerate cell both the speed integral and the chord length vanish.
    subst hEq
    simp
  have hxy_lt : x < y := lt_of_le_of_ne hxy hEq
  have hδ_nonneg : 0 ≤ δ := by
    have hx_mem : x ∈ Set.Icc x y := ⟨le_rfl, hxy⟩
    exact le_trans (by simpa using norm_nonneg (derivWithin γ (Set.Icc x y) x - v)) (hδ x hx_mem)
  have hderivCont :
      ContinuousOn (derivWithin γ (Set.Icc x y)) (Set.Icc x y) :=
    hγ.continuousOn_derivWithin (s := Set.Icc x y) (uniqueDiffOn_Icc hxy_lt) (by norm_num)
  have hderivInt :
      IntervalIntegrable (fun t : ℝ ↦ derivWithin γ (Set.Icc x y) t) volume x y :=
    hderivCont.intervalIntegrable_of_Icc hxy
  have hnormInt :
      IntervalIntegrable (fun t : ℝ ↦ ‖derivWithin γ (Set.Icc x y) t‖) volume x y :=
    hderivCont.norm.intervalIntegrable_of_Icc hxy
  have hshiftInt :
      IntervalIntegrable (fun t : ℝ ↦ derivWithin γ (Set.Icc x y) t - v) volume x y :=
    (hderivCont.sub continuousOn_const).intervalIntegrable_of_Icc hxy
  have hshiftNormInt :
      IntervalIntegrable (fun t : ℝ ↦ ‖derivWithin γ (Set.Icc x y) t - v‖) volume x y :=
    (hderivCont.sub continuousOn_const).norm.intervalIntegrable_of_Icc hxy
  have hconstNormInt :
      IntervalIntegrable (fun _ : ℝ ↦ ‖v‖ + δ) volume x y :=
    continuous_const.intervalIntegrable _ _
  have hconstShiftInt :
      IntervalIntegrable (fun _ : ℝ ↦ δ) volume x y :=
    continuous_const.intervalIntegrable _ _
  have hconstInt :
      IntervalIntegrable (fun _ : ℝ ↦ v) volume x y :=
    continuous_const.intervalIntegrable _ _
  have hderivIntegral :
      ∫ t in x..y, derivWithin γ (Set.Icc x y) t = γ y - γ x :=
    intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc hγ hxy
  have herror_eq :
      ∫ t in x..y, (derivWithin γ (Set.Icc x y) t - v) =
        γ y - γ x - (y - x) • v := by
    -- Separate the constant part of the interval derivative and rewrite the derivative integral.
    have hsub :
        ∫ t in x..y, (derivWithin γ (Set.Icc x y) t - v) =
          (∫ t in x..y, derivWithin γ (Set.Icc x y) t) - (y - x) • v := by
      simpa [intervalIntegral.integral_const] using intervalIntegral.integral_sub hderivInt hconstInt
    calc
      ∫ t in x..y, (derivWithin γ (Set.Icc x y) t - v) =
          (∫ t in x..y, derivWithin γ (Set.Icc x y) t) - (y - x) • v := hsub
      _ = γ y - γ x - (y - x) • v := by rw [hderivIntegral]
  have herror_bound :
      ‖∫ t in x..y, (derivWithin γ (Set.Icc x y) t - v)‖ ≤ δ * (y - x) := by
    -- The interval derivative oscillation is pointwise `≤ δ`, so its integral has norm
    -- bounded by `δ * (y - x)`.
    calc
      ‖∫ t in x..y, (derivWithin γ (Set.Icc x y) t - v)‖ ≤
          ∫ t in x..y, ‖derivWithin γ (Set.Icc x y) t - v‖ := by
            exact intervalIntegral.norm_integral_le_integral_norm hxy
      _ ≤ ∫ t in x..y, δ := by
            refine intervalIntegral.integral_mono_on_of_le_Ioo hxy hshiftNormInt hconstShiftInt ?_
            intro t ht
            exact hδ t ⟨ht.1.le, ht.2.le⟩
      _ = δ * (y - x) := by simpa [smul_eq_mul, mul_comm] using intervalIntegral.integral_const δ
  have hv_bound :
      (y - x) * ‖v‖ ≤ dist (γ x) (γ y) + δ * (y - x) := by
    -- Rewrite the fixed-vector contribution as the main chord plus the integral error term.
    have hsmul_eq :
        (y - x) • v =
          (γ y - γ x) - ∫ t in x..y, (derivWithin γ (Set.Icc x y) t - v) := by
      rw [herror_eq]
      abel
    calc
      (y - x) * ‖v‖ = ‖(y - x) • v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)]
      _ = ‖(γ y - γ x) - ∫ t in x..y, (derivWithin γ (Set.Icc x y) t - v)‖ := by
            rw [hsmul_eq]
      _ ≤ ‖γ y - γ x‖ + ‖∫ t in x..y, (derivWithin γ (Set.Icc x y) t - v)‖ := by
            exact norm_sub_le _ _
      _ ≤ ‖γ y - γ x‖ + δ * (y - x) := by
            gcongr
      _ = ‖γ x - γ y‖ + δ * (y - x) := by rw [norm_sub_rev]
      _ = dist (γ x) (γ y) + δ * (y - x) := by rw [dist_eq_norm]
  have hspeed_bound :
      ∫ t in x..y, ‖derivWithin γ (Set.Icc x y) t‖ ≤ (‖v‖ + δ) * (y - x) := by
    -- Pointwise, the speed cannot exceed the frozen derivative norm by more than `δ`.
    calc
      ∫ t in x..y, ‖derivWithin γ (Set.Icc x y) t‖ ≤ ∫ t in x..y, (‖v‖ + δ) := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo hxy hnormInt hconstNormInt ?_
        intro t ht
        calc
          ‖derivWithin γ (Set.Icc x y) t‖ ≤ ‖v‖ + ‖derivWithin γ (Set.Icc x y) t - v‖ := by
                simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                  norm_add_le (derivWithin γ (Set.Icc x y) t - v) v
          _ ≤ ‖v‖ + δ := by gcongr; exact hδ t ⟨ht.1.le, ht.2.le⟩
      _ = (‖v‖ + δ) * (y - x) := by
            simpa [smul_eq_mul, mul_comm] using intervalIntegral.integral_const (‖v‖ + δ)
  -- Combine the fixed-vector lower bound on the chord with the pointwise upper bound on the speed.
  linarith

omit hf

/-- Helper for Exercise 2: a unit-speed parametrization is `1`-Lipschitz on its parameter set. -/
lemma hasUnitSpeedOn_lipschitzOnWith_one
    {E : Type*} [PseudoMetricSpace E] {φ : ℝ → E} {s : Set ℝ}
    (hφ : HasUnitSpeedOn φ s) :
    LipschitzOnWith 1 φ s := by
  have hspeed : HasConstantSpeedOnWith φ s 1 := by
    simpa [HasUnitSpeedOn] using hφ
  rw [hasConstantSpeedOnWith_iff_ordered] at hspeed
  have hordered :
      ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s),
        x ≤ y → eVariationOn φ (s ∩ Set.Icc x y) = ENNReal.ofReal (y - x) := by
    intro x hx y hy hxy
    simpa using hspeed hx hy hxy
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · have hx' : x ∈ s ∩ Set.Icc x y := ⟨hx, le_rfl, hxy⟩
    have hy' : y ∈ s ∩ Set.Icc x y := ⟨hy, hxy, le_rfl⟩
    -- On an ordered pair, the unit-speed variation formula bounds the endpoint distance.
    calc
      edist (φ x) (φ y) ≤ eVariationOn φ (s ∩ Set.Icc x y) :=
        eVariationOn.edist_le φ hx' hy'
      _ = ENNReal.ofReal (y - x) := hordered hx hy hxy
      _ = edist x y := by
        simpa [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
      _ = 1 * edist x y := by simp
  · -- The reverse-ordered case follows by symmetry of the ambient distance.
    calc
      edist (φ x) (φ y) = edist (φ y) (φ x) := edist_comm _ _
      _ ≤ eVariationOn φ (s ∩ Set.Icc y x) := by
        exact eVariationOn.edist_le φ ⟨hy, le_rfl, hyx⟩ ⟨hx, hyx, le_rfl⟩
      _ = ENNReal.ofReal (x - y) := hordered hy hx hyx
      _ = edist x y := by
        simpa [edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)]
      _ = 1 * edist x y := by simp

/-- Helper for Exercise 2: the variation parameter on `Icc a b` takes values in `[0, V]`, where
`V` is the total variation on that interval. -/
lemma variation_parameter_image_subset_interval
    {E : Type*} [PseudoEMetricSpace E] {γ : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hbv : LocallyBoundedVariationOn γ (Set.Icc a b)) :
    variationOnFromTo γ (Set.Icc a b) a '' Set.Icc a b ⊆
      Set.Icc 0 (eVariationOn γ (Set.Icc a b)).toReal := by
  let v : ℝ → ℝ := variationOnFromTo γ (Set.Icc a b) a
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hmono : MonotoneOn v (Set.Icc a b) := variationOnFromTo.monotoneOn hbv ha
  intro t ht
  rcases ht with ⟨x, hx, rfl⟩
  constructor
  · -- Monotonicity from the left endpoint gives the nonnegativity of the parameter.
    have hx0 : v a ≤ v x := hmono ha hx hx.1
    simpa [v, variationOnFromTo.self] using hx0
  · -- Monotonicity up to the right endpoint bounds the parameter by the total variation.
    have hxtop : v x ≤ v b := hmono hx hb hx.2
    simpa [v, variationOnFromTo.eq_of_le (f := γ) (s := Set.Icc a b) hab] using hxtop

/-- Helper for Exercise 2: the natural parameterization on `Icc a b` has exactly the same image as
the original curve on that interval, once the parameter set is identified with the variation image.
-/
lemma naturalParameterization_image_eq_interval_image
    {E : Type*} [MetricSpace E] {γ : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hbv : LocallyBoundedVariationOn γ (Set.Icc a b)) :
    naturalParameterization γ (Set.Icc a b) a ''
        (variationOnFromTo γ (Set.Icc a b) a '' Set.Icc a b) =
      γ '' Set.Icc a b := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  ext z
  constructor
  · rintro ⟨t, ⟨x, hx, rfl⟩, rfl⟩
    -- Unfold the inverse-choice definition only after the variation parameter is known to come
    -- from the interval image.
    refine ⟨Function.invFunOn (variationOnFromTo γ (Set.Icc a b) a) (Set.Icc a b)
        (variationOnFromTo γ (Set.Icc a b) a x), ?_, ?_⟩
    · exact Function.invFunOn_apply_mem (f := variationOnFromTo γ (Set.Icc a b) a) hx
    · rfl
  · rintro ⟨x, hx, rfl⟩
    refine ⟨variationOnFromTo γ (Set.Icc a b) a x, ⟨x, hx, rfl⟩, ?_⟩
    -- The natural parameterization agrees with the original curve at matching variation values.
    exact edist_eq_zero.mp <|
      edist_naturalParameterization_eq_zero hbv ha hx

/-- Helper for Exercise 2: after reparameterizing by variation, the `1`-dimensional Hausdorff
measure of the image is bounded above by the total variation on `Icc a b`. -/
lemma hausdorffMeasure_naturalParameterization_image_le_variation
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hbv : LocallyBoundedVariationOn γ (Set.Icc a b)) :
    μH[1] (naturalParameterization γ (Set.Icc a b) a ''
        (variationOnFromTo γ (Set.Icc a b) a '' Set.Icc a b)) ≤
      eVariationOn γ (Set.Icc a b) := by
  let s : Set ℝ := variationOnFromTo γ (Set.Icc a b) a '' Set.Icc a b
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hvar : eVariationOn γ (Set.Icc a b) ≠ ⊤ := by
    simpa [BoundedVariationOn, Set.inter_self] using hbv a b ha hb
  have hunit :
      HasUnitSpeedOn (naturalParameterization γ (Set.Icc a b) a) s := by
    simpa [s] using has_unit_speed_naturalParameterization γ hbv ha
  have hLip :
      LipschitzOnWith 1 (naturalParameterization γ (Set.Icc a b) a) s :=
    hasUnitSpeedOn_lipschitzOnWith_one hunit
  -- The natural parameterization is `1`-Lipschitz on the variation image, so its image measure is
  -- controlled by the measure of the parameter interval.
  calc
    μH[1] (naturalParameterization γ (Set.Icc a b) a '' s) ≤ μH[1] s := by
      simpa [s] using hLip.hausdorffMeasure_image_le (d := (1 : ℝ)) (by norm_num)
    _ ≤ μH[1] (Set.Icc 0 (eVariationOn γ (Set.Icc a b)).toReal) := by
      exact measure_mono (variation_parameter_image_subset_interval (γ := γ) hab hbv)
    _ = eVariationOn γ (Set.Icc a b) := by
      rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]
      simp [hvar]

/-- Helper for Exercise 2: the norm of the derivative of a `C¹` curve on a closed interval is
interval-integrable. -/
lemma intervalIntegrable_norm_deriv_of_contDiffOn_Icc
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    IntervalIntegrable (fun t : ℝ ↦ ‖deriv γ t‖) volume a b := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  have hcont :
      ContinuousOn (derivWithin γ (Set.Icc a b)) (Set.Icc a b) :=
    hγ.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) (by norm_num)
  have hIntWithin :
      IntervalIntegrable (fun t : ℝ ↦ ‖derivWithin γ (Set.Icc a b) t‖) volume a b :=
    hcont.norm.intervalIntegrable_of_Icc hab
  -- On the interior of the interval, `derivWithin` agrees with the ordinary derivative.
  refine hIntWithin.congr_ae ?_
  simp only [hab, Set.uIoc_of_le]
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

/-- Helper for Exercise 2: on a `C¹` interval, each chord is bounded by the integral of the speed
over the corresponding subinterval. -/
lemma dist_le_integral_norm_deriv_of_contDiffOn_Icc
    {γ : ℝ → ℂ} {a b x y : ℝ} (hxy : x ≤ y)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    dist (γ x) (γ y) ≤ ∫ t in x..y, ‖deriv γ t‖ := by
  have hsub :
      ContDiffOn ℝ 1 γ (Set.Icc x y) := by
    -- Restrict the `C¹` regularity from the large interval to the chosen cell.
    refine hγ.mono ?_
    intro t ht
    exact ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
  have hInt : IntervalIntegrable (fun t : ℝ ↦ ‖deriv γ t‖) volume x y :=
    intervalIntegrable_norm_deriv_of_contDiffOn_Icc hxy hsub
  -- Apply the fundamental theorem of calculus and estimate the norm of the resulting integral.
  calc
    dist (γ x) (γ y) = ‖γ y - γ x‖ := by rw [dist_eq_norm, norm_sub_rev]
    _ = ‖∫ t in x..y, deriv γ t‖ := by
      rw [intervalIntegral.integral_deriv_of_contDiffOn_Icc hsub hxy]
    _ ≤ ∫ t in x..y, ‖deriv γ t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hxy

/-- Helper for Exercise 2: the Euclidean Hausdorff `1`-measure of a closed interval image is
bounded by the total variation of the curve on that interval. -/
lemma image_Icc_euclideanHausdorffMeasure_le_eVariation
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hbv : LocallyBoundedVariationOn γ (Set.Icc a b)) :
    μHE[1] (γ '' Set.Icc a b) ≤ eVariationOn γ (Set.Icc a b) := by
  -- Reparameterize by variation and use the `1`-Lipschitz natural parameterization.
  rw [euclideanHausdorffMeasure_one_eq_hausdorffMeasure_one]
  rw [← naturalParameterization_image_eq_interval_image (γ := γ) hab hbv]
  exact hausdorffMeasure_naturalParameterization_image_le_variation (γ := γ) hab hbv

/-- Helper for Exercise 2: the variation of a `C¹` curve on a closed interval is bounded by the
integral of its speed. -/
lemma eVariationOn_Icc_le_integral_norm_deriv
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    eVariationOn γ (Set.Icc a b) ≤ ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := by
  -- TODO: the remaining analytic step is to sum the subinterval chord bounds coming from
  -- `dist_le_integral_norm_deriv_of_contDiffOn_Icc` over a strict partition and then telescope
  -- the adjacent interval integrals. The current frontier isolates this from the harder geometric
  -- reverse inequality below.
  sorry

/-- Helper for Exercise 2: a `C¹` curve on `Icc a b` has finite variation on every subinterval of
`Icc a b`. -/
lemma locallyBoundedVariationOn_Icc_of_contDiffOn
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    LocallyBoundedVariationOn γ (Set.Icc a b) := by
  intro x y hx hy
  by_cases hxy : x ≤ y
  · have hinter :
        Set.Icc a b ∩ Set.Icc x y = Set.Icc x y := by
      apply Set.inter_eq_right.mpr
      intro t ht
      exact ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
    have hsub :
        ContDiffOn ℝ 1 γ (Set.Icc x y) := by
      refine hγ.mono ?_
      intro t ht
      exact ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
    obtain ⟨K, hK⟩ :=
      hsub.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
    -- On each compact subinterval, `C¹` regularity yields a Lipschitz bound, hence bounded
    -- variation.
    simpa [hinter] using
      (hK.locallyBoundedVariationOn (s := Set.Icc x y)) x y
        (by simp [hxy]) (by simp [hxy])
  · have hyx : y < x := lt_of_not_ge hxy
    -- If the ordered cell is empty, its variation is trivially finite.
    simpa [BoundedVariationOn, Set.Icc_eq_empty_of_lt hyx]

/-- Helper for Exercise 2: the remaining geometric blocker is the reverse inequality from the speed
integral of an injective `C¹` interval image to its Euclidean Hausdorff `1`-measure. -/
lemma integral_norm_deriv_Icc_le_euclideanHausdorffMeasure_image
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hinj : Set.InjOn γ (Set.Icc a b)) :
    ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) ≤ μHE[1] (γ '' Set.Icc a b) := by
  -- TODO: prove the reverse inequality by the planned fine-partition argument.
  -- The intended route is:
  -- 1. choose a fine partition of `[a, b]` on which `derivWithin γ (Set.Icc a b)` oscillates
  --    by at most `δ`;
  -- 2. apply `single_cell_speed_le_chord_add_derivWithin_oscillation` on each partition cell;
  -- 3. bound each chord by the Hausdorff measure of the corresponding cell image via
  --    `hausdorffMeasure_ge_dist_of_isPreconnected`;
  -- 4. add the cell estimates using `image_Icc_union_measure_eq_of_injOn`;
  -- 5. let `δ → 0`.
  sorry

/-- Helper for Exercise 2: for an injective `C¹` curve on a closed interval, the Euclidean
Hausdorff `1`-measure of its image equals the speed integral. -/
lemma image_Icc_euclideanHausdorffMeasure_eq_integral_norm_deriv
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hinj : Set.InjOn γ (Set.Icc a b)) :
    μHE[1] (γ '' Set.Icc a b) = ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := by
  have hbv : LocallyBoundedVariationOn γ (Set.Icc a b) :=
    locallyBoundedVariationOn_Icc_of_contDiffOn hab hγ
  -- Combine the easy upper bound with the single remaining reverse inequality.
  refine le_antisymm ?_ (integral_norm_deriv_Icc_le_euclideanHausdorffMeasure_image hab hγ hinj)
  calc
    μHE[1] (γ '' Set.Icc a b) ≤ eVariationOn γ (Set.Icc a b) :=
      image_Icc_euclideanHausdorffMeasure_le_eVariation hab hbv
    _ ≤ ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) :=
      eVariationOn_Icc_le_integral_norm_deriv hab hγ

include hf

/-- Helper for Exercise 2: the remaining source-faithful blocker is the geometric identification
of the simple boundary image length with the boundary speed integral. -/
lemma boundary_circle_param_image_length_eq
    (hR : 0 ≤ R) (hR0 : R ≠ 0)
    (hinj : Set.InjOn f (Metric.sphere (0 : ℂ) R)) :
    μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π)) =
      ENNReal.ofReal
        (R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖) := by
  -- TODO: prove this by the source route: transfer injectivity to the angular parametrization,
  -- identify the Hausdorff length of the resulting simple closed `C¹` curve, then rewrite the
  -- speed using `boundary_circle_param_speed`.
  have hinjParam :
      Set.InjOn (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Ioc (0 : ℝ) (2 * π)) :=
    boundary_circle_param_injOn (f := f) hR hR0 hinj
  have hcont :
      ContDiffOn ℝ 1 (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Icc (0 : ℝ) (2 * π)) :=
    boundary_circle_param_contDiffOn (hf := hf) hR
  have hclosed :
      (fun θ : ℝ ↦ f (circleMap 0 R θ)) (0 : ℝ) =
        (fun θ : ℝ ↦ f (circleMap 0 R θ)) (2 * π) :=
    boundary_circle_param_endpoint_eq (hf := hf)
  have hspeedIntegral :
      ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖ =
        R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖ :=
    boundary_circle_param_integral_speed_eq (hf := hf) hR
  have hhalfInj :
      Set.InjOn (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Icc (0 : ℝ) π) ∧
        Set.InjOn (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Icc π (2 * π)) :=
    boundary_circle_param_half_injOn (hf := hf) (f := f) hR hR0 hinj
  have hhalfOverlap :
      μHE[1]
          (((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) ∩
            ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π))) = 0 :=
    boundary_circle_half_image_overlap_measure_zero (hf := hf) (f := f) hR hR0 hinj
  have himageSplit :
      (fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π) =
        ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) ∪
          ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π)) :=
    boundary_circle_param_image_eq_half_union (hf := hf) (f := f) (R := R)
  have hmeasureSplit :
      μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π)) =
        μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) +
          μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π)) := by
    -- Rewrite the full image as a union, then use zero-overlap additivity.
    rw [himageSplit]
    exact boundary_circle_param_half_union_measure_eq (hf := hf) (f := f) (R := R) hR hhalfOverlap
  have hleftCont :
      ContDiffOn ℝ 1 (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Icc (0 : ℝ) π) := by
    -- Restrict the `C¹` regularity to the left half-arc.
    refine hcont.mono ?_
    intro θ hθ
    exact ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hrightCont :
      ContDiffOn ℝ 1 (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Icc π (2 * π)) := by
    -- Restrict the `C¹` regularity to the right half-arc.
    refine hcont.mono ?_
    intro θ hθ
    exact ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hleftLength :
      μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) =
        ENNReal.ofReal
          (∫ θ in (0 : ℝ)..π, ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) := by
    exact image_Icc_euclideanHausdorffMeasure_eq_integral_norm_deriv
      (show (0 : ℝ) ≤ π by linarith [Real.pi_pos]) hleftCont hhalfInj.1
  have hrightLength :
      μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π)) =
        ENNReal.ofReal
          (∫ θ in π..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) := by
    exact image_Icc_euclideanHausdorffMeasure_eq_integral_norm_deriv
      (show π ≤ 2 * π by linarith [Real.pi_pos]) hrightCont hhalfInj.2
  have hderivInt_left :
      IntervalIntegrable
        (fun θ : ℝ ↦ ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) volume 0 π :=
    intervalIntegrable_norm_deriv_of_contDiffOn_Icc
      (show (0 : ℝ) ≤ π by linarith [Real.pi_pos]) hleftCont
  have hderivInt_right :
      IntervalIntegrable
        (fun θ : ℝ ↦ ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) volume π (2 * π) :=
    intervalIntegrable_norm_deriv_of_contDiffOn_Icc
      (show π ≤ 2 * π by linarith [Real.pi_pos]) hrightCont
  have hnonneg_left :
      0 ≤ ∫ θ in (0 : ℝ)..π, ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖ := by
    exact intervalIntegral.integral_nonneg (show (0 : ℝ) ≤ π by linarith [Real.pi_pos])
      (fun θ hθ ↦ norm_nonneg _)
  have hnonneg_right :
      0 ≤ ∫ θ in π..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖ := by
    exact intervalIntegral.integral_nonneg (show π ≤ 2 * π by linarith [Real.pi_pos])
      (fun θ hθ ↦ norm_nonneg _)
  have hgeom :
      μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π)) =
        ENNReal.ofReal
          (∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) := by
    -- Route correction: the boundary proof now reduces to the generic interval theorem on the
    -- two closed half-arcs and then recombines them by adjacent-interval additivity.
    calc
      μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π)) =
          μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) +
            μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π)) := hmeasureSplit
      _ =
          ENNReal.ofReal (∫ θ in (0 : ℝ)..π, ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) +
            ENNReal.ofReal (∫ θ in π..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) := by
              rw [hleftLength, hrightLength]
      _ = ENNReal.ofReal
            ((∫ θ in (0 : ℝ)..π, ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) +
              ∫ θ in π..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) := by
              rw [← ENNReal.ofReal_add hnonneg_left hnonneg_right]
      _ = ENNReal.ofReal
            (∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) := by
              congr 1
              exact intervalIntegral.integral_add_adjacent_intervals hderivInt_left hderivInt_right
  calc
    μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π)) =
        ENNReal.ofReal
          (∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) := hgeom
    _ = ENNReal.ofReal
          (R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖) := by
            rw [hspeedIntegral]

/-- Exercise 2 (1): if `f` is holomorphic on a neighborhood of the closed disc `|z| ≤ R` and
injective on the boundary circle `|z| = R`, then the Euclidean Hausdorff length of the boundary
image `f '' sphere 0 R` is `R ∫_0^{2π} ‖f'(R e^{iθ})‖ dθ`. -/
theorem boundary_image_length_eq
    (hR : 0 ≤ R)
    (hinj : Set.InjOn f (Metric.sphere (0 : ℂ) R)) :
    μHE[1] (f '' Metric.sphere (0 : ℂ) R) =
      ENNReal.ofReal
        (R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖) := by
  -- Route correction: first rewrite the boundary as the angular image and transfer injectivity to
  -- that parametrization. The remaining work is now isolated to the simple-closed-curve
  -- Hausdorff-length bridge; the path-length-to-speed rewrite is handled separately above.
  by_cases hR0 : R = 0
  · haveI := MeasureTheory.Measure.noAtoms_hausdorff ℂ (show 0 < (1 : ℝ) by norm_num)
    simp [hR0, MeasureTheory.Measure.euclideanHausdorffMeasure_def]
  have himage :
      f '' Metric.sphere (0 : ℂ) R =
        (fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π) :=
    boundary_image_eq_circle_param_image (f := f) hR
  -- The unresolved part is now packaged as the single boundary-parametrization length theorem.
  rw [himage]
  exact boundary_circle_param_image_length_eq (hf := hf) hR hR0 hinj

/-- Exercise 2 (2): under the same hypotheses, the boundary-image length is bounded below by
`2 π R ‖f'(0)‖`. -/
theorem boundary_image_length_ge
    (hR : 0 ≤ R)
    (hinj : Set.InjOn f (Metric.sphere (0 : ℂ) R)) :
    ENNReal.ofReal (2 * π * R * ‖deriv f 0‖) ≤
      μHE[1] (f '' Metric.sphere (0 : ℂ) R) := by
  -- Rewrite the boundary length using the already-established arc-length formula.
  rw [boundary_image_length_eq (hf := hf) hR hinj]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hR0 : R = 0
  · -- The degenerate circle has zero radius, so both sides vanish.
    simp [hR0]
  have hRpos : 0 < R := lt_of_le_of_ne hR (by simpa [eq_comm] using hR0)
  have hderivDiffCont : DiffContOnCl ℂ (deriv f) (Metric.ball 0 |R|) := by
    simpa [abs_of_nonneg hR] using
      (hf.deriv.differentiableOn).diffContOnCl_ball (c := (0 : ℂ)) (R := R) subset_rfl
  have hmean : Real.circleAverage (deriv f) 0 R = deriv f 0 :=
    hderivDiffCont.circleAverage
  have hnorm :
      ‖deriv f 0‖ ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖ := by
    -- Take norms in the mean-value identity and bound the norm of the integral by the integral
    -- of the norm.
    calc
      ‖deriv f 0‖ =
          ‖(2 * π)⁻¹ • ∫ θ in (0 : ℝ)..(2 * π), deriv f (circleMap 0 R θ)‖ := by
            rw [← hmean, Real.circleAverage_def]
      _ = (2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..(2 * π), deriv f (circleMap 0 R θ)‖ := by
            have hnonneg : 0 ≤ (2 * π)⁻¹ := by positivity
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      _ ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖ := by
            exact mul_le_mul_of_nonneg_left
              (intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le)
              (by positivity)
  have hmain :
      2 * π * R * ‖deriv f 0‖ ≤
        R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖ := by
    calc
      2 * π * R * ‖deriv f 0‖ ≤ (2 * π * R) * ((2 * π)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖) := by
            exact mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖ := by
            field_simp [Real.two_pi_pos.ne', hRpos.ne']
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmain

/-- Exercise 2 (3): if `f` is holomorphic on a neighborhood of the closed disc `|z| ≤ R` and
injective on that closed disc, then the area of its image is the integral of `‖f'‖²` over the
disc. -/
theorem closed_disc_image_area_eq
    (hR : 0 ≤ R)
    (hinj : Set.InjOn f (Metric.closedBall (0 : ℂ) R)) :
    volume (f '' Metric.closedBall (0 : ℂ) R) =
      ENNReal.ofReal
        (∫ z in Metric.closedBall (0 : ℂ) R, ‖deriv f z‖ ^ 2 ∂volume) := by
  let s : Set ℂ := Metric.closedBall (0 : ℂ) R
  have hs : MeasurableSet s := measurableSet_closedBall
  have hderivWithin :
      ∀ z ∈ s, HasFDerivWithinAt f ((deriv f z) • (1 : ℂ →L[ℝ] ℂ)) s z := by
    intro z hz
    exact ((hf z hz).differentiableAt.hasDerivAt.complexToReal_fderiv).hasFDerivWithinAt
  have hlintegral :
      volume (f '' s) =
        ∫⁻ z in s, ENNReal.ofReal |(((deriv f z) • (1 : ℂ →L[ℝ] ℂ)).det)| ∂volume := by
    -- The change-of-variables formula computes the area of the injective image.
    simpa [s] using
      (MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume) hs
        hderivWithin hinj (fun _ : ℂ ↦ 1))
  have hdet :
      ∀ z : ℂ,
        ENNReal.ofReal |(((deriv f z) • (1 : ℂ →L[ℝ] ℂ)).det)| =
          ENNReal.ofReal (‖deriv f z‖ ^ 2) := by
    intro z
    rw [complex_abs_det_smul_id_eq_sq_norm]
  have hderivAnalytic : AnalyticOnNhd ℂ (deriv f) s := by
    simpa [s] using
      (AnalyticOnNhd.deriv (𝕜 := ℂ) (F := ℂ) (f := f) (s := s) hf)
  have hcontDeriv : ContinuousOn (deriv f) s := hderivAnalytic.continuousOn
  have hcont :
      ContinuousOn (fun z : ℂ ↦ ‖deriv f z‖ ^ 2) s := by
    simpa using hcontDeriv.norm.pow 2
  have hscompact : IsCompact s := by
    simpa [s] using isCompact_closedBall (x := (0 : ℂ)) (r := R)
  have hint :
      IntegrableOn (fun z : ℂ ↦ ‖deriv f z‖ ^ 2) s volume :=
    hcont.integrableOn_compact hscompact
  -- Convert the nonnegative `lintegral` back to the ordinary real integral.
  calc
    volume (f '' s) =
        ∫⁻ z in s, ENNReal.ofReal (‖deriv f z‖ ^ 2) ∂volume := by
          rw [hlintegral]
          refine setLIntegral_congr_fun hs ?_
          intro z hz
          exact hdet z
    _ = ENNReal.ofReal (∫ z in s, ‖deriv f z‖ ^ 2 ∂volume) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hint]
          exact Filter.Eventually.of_forall fun z ↦ sq_nonneg ‖deriv f z‖
    _ = ENNReal.ofReal (∫ z in Metric.closedBall (0 : ℂ) R, ‖deriv f z‖ ^ 2 ∂volume) := by
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

/-- Exercise 2 (4): under the same hypotheses, the image area is bounded below by
`π R² ‖f'(0)‖²`. -/
theorem closed_disc_image_area_ge
    (hR : 0 ≤ R)
    (hinj : Set.InjOn f (Metric.closedBall (0 : ℂ) R)) :
    ENNReal.ofReal (π * R ^ 2 * ‖deriv f 0‖ ^ 2) ≤
      volume (f '' Metric.closedBall (0 : ℂ) R) := by
  have hderivAnalytic : AnalyticOnNhd ℂ (deriv f) (Metric.closedBall (0 : ℂ) R) := by
    simpa using
      (AnalyticOnNhd.deriv (𝕜 := ℂ) (F := ℂ) (f := f) (s := Metric.closedBall (0 : ℂ) R) hf)
  have hcontDeriv : ContinuousOn (deriv f) (Metric.closedBall (0 : ℂ) R) :=
    hderivAnalytic.continuousOn
  have hsqCont : ContinuousOn (fun z : ℂ ↦ ‖deriv f z‖ ^ 2) (Metric.closedBall (0 : ℂ) R) := by
    simpa using hcontDeriv.norm.pow 2
  have hcircleAverageCont :
      ContinuousOn (Real.circleAverage (fun z : ℂ ↦ ‖deriv f z‖ ^ 2) 0) (Set.Icc (0 : ℝ) R) := by
    -- The circle average varies continuously with the radius on the closed interval `[0, R]`.
    have hsqCont' :
        ContinuousOn (fun z : ℂ ↦ ‖deriv f z‖ ^ 2)
          {z : ℂ | ‖z - (0 : ℂ)‖ ∈ Set.Icc (0 : ℝ) R} := by
      simpa [Metric.closedBall, Metric.mem_closedBall, dist_eq_norm, sub_zero] using hsqCont
    exact Real.ContinuousOn.circleAverage (s := Set.Icc (0 : ℝ) R) (c := (0 : ℂ))
      hsqCont' fun r hr ↦ hr.1
  let avg : ℝ → ℝ := fun r ↦ Real.circleAverage (fun z : ℂ ↦ ‖deriv f z‖ ^ 2) 0 r
  have havgInt :
      ContinuousOn (fun r : ℝ ↦ (2 * π) * (r * avg r)) (Set.Icc (0 : ℝ) R) := by
    -- Repackage the angular integral through the continuous circle average.
    intro r hr
    exact continuousAt_const.continuousWithinAt.mul ((continuousOn_id.mul hcircleAverageCont) r hr)
  have hleftInt :
      IntervalIntegrable (fun r : ℝ ↦ (2 * π) * (r * ‖deriv f 0‖ ^ 2)) volume 0 R :=
    (continuous_const.mul (continuous_id.mul continuous_const)).intervalIntegrable _ _
  have hrightInt :
      IntervalIntegrable
        (fun r : ℝ ↦ r * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2) volume 0 R := by
    have hEq :
        Set.EqOn
          (fun r : ℝ ↦ r * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2)
          (fun r : ℝ ↦ (2 * π) * (r * avg r))
          (Set.Icc (0 : ℝ) R) := by
      intro r hr
      -- Rewrite the angular integral through `circleAverage`.
      change r * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2 =
        (2 * π) *
          (r * ((2 * π)⁻¹ *
            ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2))
      field_simp [Real.pi_ne_zero]
    exact (havgInt.congr hEq).intervalIntegrable_of_Icc hR
  have hmono :
      ∫ r in (0 : ℝ)..R, (2 * π) * (r * ‖deriv f 0‖ ^ 2) ≤
        ∫ r in (0 : ℝ)..R, r * ∫ θ in (0 : ℝ)..(2 * π),
          ‖deriv f (circleMap 0 r θ)‖ ^ 2 := by
    -- Integrate the radiuswise Cauchy-Schwarz bound over `0 ≤ r ≤ R`.
    apply intervalIntegral.integral_mono_on_of_le_Ioo hR hleftInt hrightInt
    intro r hr
    have hsquare :
        ‖deriv f 0‖ ^ 2 ≤
          (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2 :=
      sq_norm_deriv_zero_le_circle_average_sq_norm_deriv (hf := hf) hr.1.le hr.2.le
    have hr_nonneg : 0 ≤ r := hr.1.le
    have hfactor :
        (2 * π) * (r * ‖deriv f 0‖ ^ 2) ≤
          (2 * π) * (r * ((2 * π)⁻¹ *
            ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsquare hr_nonneg)
        (by positivity)
    calc
      (2 * π) * (r * ‖deriv f 0‖ ^ 2) ≤
          (2 * π) * (r * ((2 * π)⁻¹ *
            ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2)) := hfactor
      _ = r * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2 := by
            ring_nf
            field_simp [Real.two_pi_pos.ne']
  have hleft :
      ∫ r in (0 : ℝ)..R, (2 * π) * (r * ‖deriv f 0‖ ^ 2) =
        π * R ^ 2 * ‖deriv f 0‖ ^ 2 := by
    -- The radial weight integrates to `R² / 2`.
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_mul_const]
    rw [show ∫ r in (0 : ℝ)..R, r = ∫ r in (0 : ℝ)..R, r ^ 1 by
      congr with r
      simp]
    rw [integral_pow]
    ring
  rw [closed_disc_image_area_eq (hf := hf) hR hinj]
  apply ENNReal.ofReal_le_ofReal
  rw [closedBall_integral_sq_norm_deriv_eq_polar (f := f) (R := R) hR]
  rw [polar_sq_norm_deriv_setIntegral_eq_radius_angleIntegral (hf := hf) (f := f) (R := R) hR]
  exact hleft.symm.le.trans hmono

end
