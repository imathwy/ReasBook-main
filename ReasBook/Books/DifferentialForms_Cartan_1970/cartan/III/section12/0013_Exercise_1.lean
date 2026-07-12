import Mathlib

-- Domain-style sampling:
-- - `source-facing`: the two weighted unit-circle integral identities below.
-- - `core/canonical`: `DiffContOnCl ℂ f (Metric.ball 0 1)`, together with the circle-average and
--   Cauchy-derivative owners already in mathlib for functions holomorphic on a neighborhood of the
--   closed unit disc.
-- - `bridge/view`: restricting `AnalyticOn ℂ f (Metric.ball 0 R)` for `R > 1` to that canonical
--   unit-disc owner.

open MeasureTheory
open scoped Real

noncomputable section

/-- Core/canonical bridge for Exercise 1: analyticity on a disc of radius `R > 1` restricts to the
canonical `DiffContOnCl` owner on the unit disc. -/
theorem diffContOnCl_unitDisc_of_analyticOn_ball
    {f : ℂ → ℂ} {R : ℝ}
    (hR : (1 : ℝ) < R)
    (hf : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R)) :
    DiffContOnCl ℂ f (Metric.ball (0 : ℂ) 1) := by
  exact hf.differentiableOn.diffContOnCl_ball <| Metric.closedBall_subset_ball hR

/-- Helper for Exercise 1: the reciprocal of `cos θ + i sin θ` is `cos θ - i sin θ`. -/
lemma cos_add_sin_mul_I_inv (θ : ℝ) :
    (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I)⁻¹ =
      Complex.cos (θ : ℂ) - Complex.sin (θ : ℂ) * Complex.I := by
  apply inv_eq_of_mul_eq_one_right
  calc
    (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I) *
        (Complex.cos (θ : ℂ) - Complex.sin (θ : ℂ) * Complex.I)
      = Complex.cos (θ : ℂ) ^ 2 + Complex.sin (θ : ℂ) ^ 2 := by
          ring_nf
          simp [Complex.I_sq]
    _ = 1 := by
          exact Complex.cos_sq_add_sin_sq (θ : ℂ)

/-- Helper for Exercise 1: on the unit circle, the cosine half-angle weight is the Laurent weight
`2 + z + z⁻¹`. -/
lemma unit_circle_cos_sq_weight_as_laurent (θ : ℝ) :
    (4 : ℂ) * (((Real.cos (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) =
      2 + circleMap 0 1 θ + (circleMap 0 1 θ)⁻¹ := by
  -- First rewrite the trigonometric weight into the standard half-angle form `2 + 2 cos θ`.
  calc
    (4 : ℂ) * (((Real.cos (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) =
        4 * Complex.cos ((θ : ℂ) / 2) ^ 2 := by
      simp [Complex.ofReal_cos]
    _ = 2 * (1 + Complex.cos (θ : ℂ)) := by
      rw [Complex.cos_sq]
      rw [show (2 : ℂ) * ((θ : ℂ) / 2) = θ by field_simp]
      ring
    _ = 2 + circleMap 0 1 θ + (circleMap 0 1 θ)⁻¹ := by
      -- Then identify `z + z⁻¹` with `2 cos θ` on the unit circle.
      simp [circleMap_zero, Complex.exp_mul_I, cos_add_sin_mul_I_inv]
      ring

/-- Helper for Exercise 1: on the unit circle, the sine half-angle weight is the Laurent weight
`2 - z - z⁻¹`. -/
lemma unit_circle_sin_sq_weight_as_laurent (θ : ℝ) :
    (4 : ℂ) * (((Real.sin (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) =
      2 - circleMap 0 1 θ - (circleMap 0 1 θ)⁻¹ := by
  -- First rewrite the trigonometric weight into the standard half-angle form `2 - 2 cos θ`.
  calc
    (4 : ℂ) * (((Real.sin (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) =
        4 * Complex.sin ((θ : ℂ) / 2) ^ 2 := by
      simp [Complex.ofReal_sin]
    _ = 4 * (1 - Complex.cos ((θ : ℂ) / 2) ^ 2) := by
      rw [Complex.sin_sq]
    _ = 2 * (1 - Complex.cos (θ : ℂ)) := by
      rw [Complex.cos_sq]
      rw [show (2 : ℂ) * ((θ : ℂ) / 2) = θ by field_simp]
      ring
    _ = 2 - circleMap 0 1 θ - (circleMap 0 1 θ)⁻¹ := by
      -- Then identify `z + z⁻¹` with `2 cos θ` on the unit circle.
      simp [circleMap_zero, Complex.exp_mul_I, cos_add_sin_mul_I_inv]
      ring

/-- Helper for Exercise 1: the scaled first-derivative Cauchy formula on the unit circle. -/
lemma unit_circle_scaled_deriv_circle_integral
    {f : ℂ → ℂ}
    (hd : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) 1)) :
    ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(0, 1), (1 / (z - 0) ^ 2) • f z) =
      deriv f 0 := by
  -- Put the derivative Cauchy formula into the normalized contour shape used later.
  calc
    ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(0, 1), (1 / (z - 0) ^ 2) • f z)
      = ((2 * π * Complex.I : ℂ)⁻¹ • ((2 * π * Complex.I : ℂ) • deriv f 0)) := by
          rw [hd.deriv_eq_smul_circleIntegral (show (0 : ℝ) < 1 by norm_num)]
    _ = deriv f 0 := by
          simpa using inv_smul_smul₀ Complex.two_pi_I_ne_zero (deriv f 0)

/-- Helper for Exercise 1: away from the origin, the plus Laurent kernel splits into the Cauchy
value term, the holomorphic term, and the derivative kernel term. -/
lemma plus_laurent_cauchy_kernel_split
    {f : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 0) :
    (z - 0)⁻¹ • ((2 + z + z⁻¹) * f z) =
      2 • ((z - 0)⁻¹ • f z) + f z + (1 / (z - 0) ^ 2) • f z := by
  -- Collapse the Laurent algebra before moving under the contour integral.
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, sub_zero]
  field_simp [hz]
  calc
    (z * (2 + z) + 1) * f z = z * f z * 2 + z ^ 2 * f z + f z := by
      ring
    _ = z ^ 2 * (2 • (f z / z) + f z) + f z := by
      have hz_cancel : f z * z ^ 2 * z⁻¹ * 2 = f z * z * 2 := by
        calc
          f z * z ^ 2 * z⁻¹ * 2 = f z * z * (z * z⁻¹) * 2 := by
            rw [pow_two]
            ring
          _ = f z * z * 2 := by
            rw [mul_inv_cancel₀ hz, mul_one]
      field_simp [hz]
      calc
        f z * (z * (2 + z) + 1) = f z + f z * z * 2 + f z * z ^ 2 := by
          ring
        _ = f z + f z * z ^ 2 + f z * z ^ 2 * z⁻¹ * 2 := by
          rw [hz_cancel]
          ring
        _ = z ^ 2 * (2 • (f z / z) + f z) + f z := by
          ring

/-- Helper for Exercise 1: away from the origin, the minus Laurent kernel splits into the Cauchy
value term, the holomorphic term, and the derivative kernel term with reversed signs. -/
lemma minus_laurent_cauchy_kernel_split
    {f : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 0) :
    (z - 0)⁻¹ • ((2 - z - z⁻¹) * f z) =
      2 • ((z - 0)⁻¹ • f z) - f z - (1 / (z - 0) ^ 2) • f z := by
  -- Collapse the Laurent algebra before moving under the contour integral.
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, sub_zero]
  field_simp [hz]
  calc
    (z * (2 - z) - 1) * f z = z * f z * 2 - z ^ 2 * f z - f z := by
      ring
    _ = z ^ 2 * (2 • (f z / z) - f z) - f z := by
      have hz_cancel : f z * z ^ 2 * z⁻¹ * 2 = f z * z * 2 := by
        calc
          f z * z ^ 2 * z⁻¹ * 2 = f z * z * (z * z⁻¹) * 2 := by
            rw [pow_two]
            ring
          _ = f z * z * 2 := by
            rw [mul_inv_cancel₀ hz, mul_one]
      field_simp [hz]
      calc
        f z * (z * (2 - z) - 1) = -f z + f z * z * 2 - f z * z ^ 2 := by
          ring
        _ = -f z - f z * z ^ 2 + f z * z ^ 2 * z⁻¹ * 2 := by
          rw [hz_cancel]
          ring
        _ = z ^ 2 * (2 • (f z / z) - f z) - f z := by
          ring

/-- Helper for Exercise 1: the Laurent weight `2 + z + z⁻¹` on the unit circle extracts
`2 f(0) + f'(0)` from the Cauchy integral. -/
lemma unit_circle_plus_laurent_circle_integral
    {f : ℂ → ℂ}
    (hd : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) 1)) :
    ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(0, 1), (z - 0)⁻¹ • ((2 + z + z⁻¹) * f z)) =
      2 * f 0 + deriv f 0 := by
  let cauchyTerm : ℂ → ℂ := fun z ↦ (z - 0)⁻¹ • f z
  let derivTerm : ℂ → ℂ := fun z ↦ (1 / (z - 0) ^ 2) • f z
  have hsub : Metric.sphere (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1 :=
    Metric.sphere_subset_closedBall
  have hcont_f : ContinuousOn f (Metric.sphere (0 : ℂ) 1) :=
    (hd.continuousOn_ball).mono hsub
  have hcont_cauchy_kernel :
      ContinuousOn (fun z : ℂ ↦ (z - 0)⁻¹) (Metric.sphere (0 : ℂ) 1) := by
    -- The Cauchy kernel is continuous on the boundary circle because the pole stays at the center.
    refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
    intro z hz
    exact sub_ne_zero.2 (Metric.ne_of_mem_sphere hz one_ne_zero)
  have hcont_deriv_kernel :
      ContinuousOn (fun z : ℂ ↦ (1 / (z - 0) ^ 2 : ℂ)) (Metric.sphere (0 : ℂ) 1) := by
    -- The squared Cauchy kernel is continuous on the boundary circle for the same reason.
    have hpow :
        ContinuousOn (fun z : ℂ ↦ (((z - 0) ^ 2 : ℂ)⁻¹)) (Metric.sphere (0 : ℂ) 1) := by
      refine ((continuousOn_id.sub continuousOn_const).pow 2).inv₀ ?_
      intro z hz
      exact pow_ne_zero 2 (sub_ne_zero.2 (Metric.ne_of_mem_sphere hz one_ne_zero))
    simpa [one_div] using hpow
  have hcauchy : CircleIntegrable cauchyTerm 0 1 := by
    -- Each contour term is integrable because it is continuous on the unit circle.
    refine ContinuousOn.circleIntegrable (show (0 : ℝ) ≤ 1 by norm_num) ?_
    simpa [cauchyTerm] using hcont_cauchy_kernel.smul hcont_f
  have hderiv : CircleIntegrable derivTerm 0 1 := by
    refine ContinuousOn.circleIntegrable (show (0 : ℝ) ≤ 1 by norm_num) ?_
    simpa [derivTerm] using hcont_deriv_kernel.smul hcont_f
  have hbase : CircleIntegrable f 0 1 :=
    ContinuousOn.circleIntegrable (show (0 : ℝ) ≤ 1 by norm_num) hcont_f
  have hscaled : CircleIntegrable (fun z ↦ (2 : ℂ) • cauchyTerm z) 0 1 := by
    simpa using hcauchy.const_smul (a := (2 : ℂ))
  let I1 : ℂ := ∮ z in C(0, 1), cauchyTerm z
  let I2 : ℂ := ∮ z in C(0, 1), f z
  let I3 : ℂ := ∮ z in C(0, 1), derivTerm z
  let I23 : ℂ := ∮ z in C(0, 1), f z + derivTerm z
  have hsplit :
      ∮ z in C(0, 1), (z - 0)⁻¹ • ((2 + z + z⁻¹) * f z) =
        ∮ z in C(0, 1), 2 • cauchyTerm z + f z + derivTerm z := by
    -- Replace the original Laurent kernel by the explicit three-piece split on the boundary.
    refine circleIntegral.integral_congr (show (0 : ℝ) ≤ 1 by norm_num) ?_
    intro z hz
    simpa [cauchyTerm, derivTerm] using
      plus_laurent_cauchy_kernel_split (f := f) (z := z)
        (Metric.ne_of_mem_sphere hz one_ne_zero)
  have hdecompose :
      ∮ z in C(0, 1), 2 • cauchyTerm z + f z + derivTerm z =
        (2 • I1 + I2) + I3 := by
    have hsum :
        I23 = I2 + I3 := by
      simpa [I23, I2, I3] using circleIntegral.integral_add hbase hderiv
    have hsmul :
        ∮ z in C(0, 1), (2 : ℂ) • cauchyTerm z = 2 • I1 := by
      calc
        ∮ z in C(0, 1), (2 : ℂ) • cauchyTerm z
          = ∮ z in C(0, 1), cauchyTerm z + cauchyTerm z := by
              refine circleIntegral.integral_congr (show (0 : ℝ) ≤ 1 by norm_num) ?_
              intro z hz
              simp [smul_eq_mul, two_mul]
        _ = (∮ z in C(0, 1), cauchyTerm z) + ∮ z in C(0, 1), cauchyTerm z := by
              exact circleIntegral.integral_add hcauchy hcauchy
        _ = 2 * ∮ z in C(0, 1), cauchyTerm z := by
              ring
        _ = 2 • I1 := by
              change 2 * ∮ z in C(0, 1), cauchyTerm z = 2 • ∮ z in C(0, 1), cauchyTerm z
              simp [two_mul]
    -- Separate the three contour pieces so that the Cauchy owners apply directly.
    calc
      ∮ z in C(0, 1), 2 • cauchyTerm z + f z + derivTerm z
        = ∮ z in C(0, 1), (2 : ℂ) • cauchyTerm z + (f z + derivTerm z) := by
            refine circleIntegral.integral_congr (show (0 : ℝ) ≤ 1 by norm_num) ?_
            intro z hz
            simp [add_assoc]
      _ = (∮ z in C(0, 1), (2 : ℂ) • cauchyTerm z) +
            I23 := by
            change ∮ z in C(0, 1), (2 : ℂ) • cauchyTerm z + (f z + derivTerm z) =
              (∮ z in C(0, 1), (2 : ℂ) • cauchyTerm z) +
                ∮ z in C(0, 1), f z + derivTerm z
            exact circleIntegral.integral_add hscaled (hbase.add hderiv)
      _ = 2 • I1 + I23 := by
            rw [hsmul]
      _ = 2 • I1 + (I2 + I3) := by
            rw [hsum]
      _ = (2 • I1 + I2) + I3 := by
            exact (add_assoc (2 • I1) I2 I3).symm
  have hcauchy_value :
      ((2 * π * Complex.I : ℂ)⁻¹ • I1) = f 0 := by
    have hw0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      exact Metric.mem_ball_self zero_lt_one
    simpa [I1, cauchyTerm] using hd.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw0
  have hzero_integral : I2 = 0 := by
    simpa [I2] using hd.circleIntegral_eq_zero (show (0 : ℝ) ≤ 1 by norm_num)
  -- Evaluate the three separated contour pieces by the value, zero, and derivative Cauchy formulas.
  calc
    ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(0, 1), (z - 0)⁻¹ • ((2 + z + z⁻¹) * f z))
      = ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(0, 1), 2 • cauchyTerm z + f z + derivTerm z) := by
          rw [hsplit]
    _ = ((2 * π * Complex.I : ℂ)⁻¹ • ((2 • I1 + I2) + I3)) := by
          rw [hdecompose]
    _ = ((2 * π * Complex.I : ℂ)⁻¹ • (2 • I1)) +
          (((2 * π * Complex.I : ℂ)⁻¹) • I2 +
            ((2 * π * Complex.I : ℂ)⁻¹) • I3) := by
          simp [smul_eq_mul, add_assoc]
          ring
    _ = 2 • (((2 * π * Complex.I : ℂ)⁻¹) • I1) +
          ((2 * π * Complex.I : ℂ)⁻¹) • I2 +
          ((2 * π * Complex.I : ℂ)⁻¹) • I3 := by
          simp [smul_eq_mul]
          ring
    _ = 2 • f 0 + ((2 * π * Complex.I : ℂ)⁻¹) • I2 +
          ((2 * π * Complex.I : ℂ)⁻¹) • I3 := by
          rw [hcauchy_value]
    _ = 2 • f 0 + ((2 * π * Complex.I : ℂ)⁻¹) • 0 +
          ((2 * π * Complex.I : ℂ)⁻¹) • I3 := by
          rw [hzero_integral]
    _ = 2 * f 0 + deriv f 0 := by
          rw [unit_circle_scaled_deriv_circle_integral hd]
          simp [smul_eq_mul]

/-- Helper for Exercise 1: the Laurent weight `2 - z - z⁻¹` on the unit circle extracts
`2 f(0) - f'(0)` from the Cauchy integral. -/
lemma unit_circle_minus_laurent_circle_integral
    {f : ℂ → ℂ}
    (hd : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) 1)) :
    ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(0, 1), (z - 0)⁻¹ • ((2 - z - z⁻¹) * f z)) =
      2 * f 0 - deriv f 0 := by
  let cauchyTerm : ℂ → ℂ := fun z ↦ (z - 0)⁻¹ • f z
  let derivTerm : ℂ → ℂ := fun z ↦ (1 / (z - 0) ^ 2) • f z
  have hsub : Metric.sphere (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1 :=
    Metric.sphere_subset_closedBall
  have hcont_f : ContinuousOn f (Metric.sphere (0 : ℂ) 1) :=
    (hd.continuousOn_ball).mono hsub
  have hcont_cauchy_kernel :
      ContinuousOn (fun z : ℂ ↦ (z - 0)⁻¹) (Metric.sphere (0 : ℂ) 1) := by
    -- The Cauchy kernel is continuous on the boundary circle because the pole stays at the center.
    refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
    intro z hz
    exact sub_ne_zero.2 (Metric.ne_of_mem_sphere hz one_ne_zero)
  have hcont_deriv_kernel :
      ContinuousOn (fun z : ℂ ↦ (1 / (z - 0) ^ 2 : ℂ)) (Metric.sphere (0 : ℂ) 1) := by
    -- The squared Cauchy kernel is continuous on the boundary circle for the same reason.
    have hpow :
        ContinuousOn (fun z : ℂ ↦ (((z - 0) ^ 2 : ℂ)⁻¹)) (Metric.sphere (0 : ℂ) 1) := by
      refine ((continuousOn_id.sub continuousOn_const).pow 2).inv₀ ?_
      intro z hz
      exact pow_ne_zero 2 (sub_ne_zero.2 (Metric.ne_of_mem_sphere hz one_ne_zero))
    simpa [one_div] using hpow
  have hcauchy : CircleIntegrable cauchyTerm 0 1 := by
    -- Each contour term is integrable because it is continuous on the unit circle.
    refine ContinuousOn.circleIntegrable (show (0 : ℝ) ≤ 1 by norm_num) ?_
    simpa [cauchyTerm] using hcont_cauchy_kernel.smul hcont_f
  have hderiv : CircleIntegrable derivTerm 0 1 := by
    refine ContinuousOn.circleIntegrable (show (0 : ℝ) ≤ 1 by norm_num) ?_
    simpa [derivTerm] using hcont_deriv_kernel.smul hcont_f
  have hbase : CircleIntegrable f 0 1 :=
    ContinuousOn.circleIntegrable (show (0 : ℝ) ≤ 1 by norm_num) hcont_f
  have hscaled : CircleIntegrable (fun z ↦ (2 : ℂ) • cauchyTerm z) 0 1 := by
    simpa using hcauchy.const_smul (a := (2 : ℂ))
  let I1 : ℂ := ∮ z in C(0, 1), cauchyTerm z
  let I2 : ℂ := ∮ z in C(0, 1), f z
  let I3 : ℂ := ∮ z in C(0, 1), derivTerm z
  have hsplit :
      ∮ z in C(0, 1), (z - 0)⁻¹ • ((2 - z - z⁻¹) * f z) =
        ∮ z in C(0, 1), 2 • cauchyTerm z - f z - derivTerm z := by
    -- Replace the original Laurent kernel by the explicit three-piece split on the boundary.
    refine circleIntegral.integral_congr (show (0 : ℝ) ≤ 1 by norm_num) ?_
    intro z hz
    simpa [cauchyTerm, derivTerm] using
      minus_laurent_cauchy_kernel_split (f := f) (z := z)
        (Metric.ne_of_mem_sphere hz one_ne_zero)
  have hdecompose :
      ∮ z in C(0, 1), 2 • cauchyTerm z - f z - derivTerm z =
        (2 • I1 - I2) - I3 := by
    have hsmul :
        ∮ z in C(0, 1), (2 : ℂ) • cauchyTerm z = 2 • I1 := by
      calc
        ∮ z in C(0, 1), (2 : ℂ) • cauchyTerm z
          = ∮ z in C(0, 1), cauchyTerm z + cauchyTerm z := by
              refine circleIntegral.integral_congr (show (0 : ℝ) ≤ 1 by norm_num) ?_
              intro z hz
              simp [smul_eq_mul, two_mul]
        _ = (∮ z in C(0, 1), cauchyTerm z) + ∮ z in C(0, 1), cauchyTerm z := by
              exact circleIntegral.integral_add hcauchy hcauchy
        _ = 2 * ∮ z in C(0, 1), cauchyTerm z := by
              ring
        _ = 2 • I1 := by
              change 2 * ∮ z in C(0, 1), cauchyTerm z = 2 • ∮ z in C(0, 1), cauchyTerm z
              simp [two_mul]
    have hsum :
        ∮ z in C(0, 1), (2 : ℂ) • cauchyTerm z - f z =
          2 • I1 - I2 := by
      have hsub : ∮ z in C(0, 1), (2 : ℂ) • cauchyTerm z - f z =
          (∮ z in C(0, 1), (2 : ℂ) • cauchyTerm z) - I2 := by
        simpa [I2] using circleIntegral.integral_sub hscaled hbase
      rw [hsub, hsmul]
    -- Separate the three contour pieces so that the same Cauchy owners apply with opposite signs.
    calc
      ∮ z in C(0, 1), 2 • cauchyTerm z - f z - derivTerm z
        = ∮ z in C(0, 1), ((2 : ℂ) • cauchyTerm z - f z) - derivTerm z := by
            refine circleIntegral.integral_congr (show (0 : ℝ) ≤ 1 by norm_num) ?_
            intro z hz
            simp [sub_eq_add_neg, add_assoc]
      _ = (∮ z in C(0, 1), (2 : ℂ) • cauchyTerm z - f z) - ∮ z in C(0, 1), derivTerm z := by
            simpa using circleIntegral.integral_sub (hscaled.sub hbase) hderiv
      _ = (2 • I1 - I2) - I3 := by
            rw [hsum]
  have hw0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    exact Metric.mem_ball_self zero_lt_one
  have hcauchy_value :
      ((2 * π * Complex.I : ℂ)⁻¹ • I1) = f 0 := by
    simpa [I1, cauchyTerm] using hd.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw0
  have hzero_integral : I2 = 0 := by
    simpa [I2] using hd.circleIntegral_eq_zero (show (0 : ℝ) ≤ 1 by norm_num)
  -- Evaluate the three separated contour pieces by the value, zero, and derivative Cauchy formulas.
  calc
    ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(0, 1), (z - 0)⁻¹ • ((2 - z - z⁻¹) * f z))
      = ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(0, 1), 2 • cauchyTerm z - f z - derivTerm z) := by
          rw [hsplit]
    _ = ((2 * π * Complex.I : ℂ)⁻¹ • ((2 • I1 - I2) - I3)) := by
          rw [hdecompose]
    _ = ((2 * π * Complex.I : ℂ)⁻¹ • (2 • I1)) -
          (((2 * π * Complex.I : ℂ)⁻¹) • I2) -
          (((2 * π * Complex.I : ℂ)⁻¹) • I3) := by
          simp [smul_eq_mul, sub_eq_add_neg, add_assoc]
          ring
    _ = 2 • (((2 * π * Complex.I : ℂ)⁻¹) • I1) -
          ((2 * π * Complex.I : ℂ)⁻¹) • I2 -
          ((2 * π * Complex.I : ℂ)⁻¹) • I3 := by
          simp [smul_eq_mul]
          ring
    _ = 2 • f 0 - ((2 * π * Complex.I : ℂ)⁻¹) • I2 -
          ((2 * π * Complex.I : ℂ)⁻¹) • I3 := by
          rw [hcauchy_value]
    _ = 2 • f 0 - ((2 * π * Complex.I : ℂ)⁻¹) • 0 -
          ((2 * π * Complex.I : ℂ)⁻¹) • I3 := by
          rw [hzero_integral]
    _ = 2 * f 0 - deriv f 0 := by
          rw [unit_circle_scaled_deriv_circle_integral hd]
          simp [smul_eq_mul, sub_eq_add_neg]

/-- Exercise 1 (1): if `f` is holomorphic on `|z| < R` for some `R > 1`, then the weighted unit
circle integral with weight `cos² (θ / 2)` equals `2 f(0) + f'(0)`. -/
theorem unit_circle_cos_sq_integral_eq_two_apply_zero_add_deriv
    {f : ℂ → ℂ} {R : ℝ}
    (hR : (1 : ℝ) < R)
    (hf : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R)) :
    ((2 / Real.pi : ℂ) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (((Real.cos (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * f (circleMap 0 1 θ)) =
      2 * f 0 + deriv f 0 := by
  have hd : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) 1) :=
    diffContOnCl_unitDisc_of_analyticOn_ball hR hf
  let g : ℂ → ℂ := fun z ↦ (2 + z + z⁻¹) * f z
  have hscalar :
      ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (4 : ℂ)) = (2 / Real.pi : ℂ) := by
    have hscalar_real : ((2 * Real.pi)⁻¹ : ℝ) * 4 = 2 / Real.pi := by
      field_simp [Real.pi_ne_zero]
      ring
    exact_mod_cast hscalar_real
  have haverage :
      Real.circleAverage g 0 1 =
        ((2 / Real.pi : ℂ) *
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (((Real.cos (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * f (circleMap 0 1 θ)) := by
    -- Translate the Laurent weight back to the textbook half-angle average.
    calc
      Real.circleAverage g 0 1
        = ((2 * Real.pi)⁻¹ : ℝ) •
            ∫ θ in (0 : ℝ)..(2 * Real.pi), g (circleMap 0 1 θ) := by
              rw [Real.circleAverage_def]
      _ = ((2 * Real.pi)⁻¹ : ℝ) •
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              (4 : ℂ) *
                ((((Real.cos (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * f (circleMap 0 1 θ)) := by
              have hpointwise :
                  (fun θ : ℝ ↦ g (circleMap 0 1 θ)) =
                    fun θ : ℝ ↦
                      (4 : ℂ) *
                        ((((Real.cos (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * f (circleMap 0 1 θ)) := by
                  funext θ
                  dsimp [g]
                  rw [← unit_circle_cos_sq_weight_as_laurent θ]
                  ring
              rw [hpointwise]
      _ = ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (4 : ℂ)) *
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              (((Real.cos (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * f (circleMap 0 1 θ) := by
              rw [intervalIntegral.integral_const_mul]
              simp [mul_assoc]
      _ = ((2 / Real.pi : ℂ) *
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              (((Real.cos (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * f (circleMap 0 1 θ)) := by
              rw [hscalar]
  -- Apply the circle-average/contour bridge and then the normalized Laurent contour formula.
  calc
    ((2 / Real.pi : ℂ) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (((Real.cos (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * f (circleMap 0 1 θ))
      = Real.circleAverage g 0 1 := by
          rw [haverage]
    _ = ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(0, 1), (z - 0)⁻¹ • g z) := by
          rw [Real.circleAverage_eq_circleIntegral one_ne_zero]
    _ = 2 * f 0 + deriv f 0 := by
          simpa [g] using unit_circle_plus_laurent_circle_integral hd

/-- Exercise 1 (2): if `f` is holomorphic on `|z| < R` for some `R > 1`, then the weighted unit
circle integral with weight `sin² (θ / 2)` equals `2 f(0) - f'(0)`. -/
theorem unit_circle_sin_sq_integral_eq_two_apply_zero_sub_deriv
    {f : ℂ → ℂ} {R : ℝ}
    (hR : (1 : ℝ) < R)
    (hf : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R)) :
    ((2 / Real.pi : ℂ) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (((Real.sin (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * f (circleMap 0 1 θ)) =
      2 * f 0 - deriv f 0 := by
  have hd : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) 1) :=
    diffContOnCl_unitDisc_of_analyticOn_ball hR hf
  let g : ℂ → ℂ := fun z ↦ (2 - z - z⁻¹) * f z
  have hscalar :
      ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (4 : ℂ)) = (2 / Real.pi : ℂ) := by
    have hscalar_real : ((2 * Real.pi)⁻¹ : ℝ) * 4 = 2 / Real.pi := by
      field_simp [Real.pi_ne_zero]
      ring
    exact_mod_cast hscalar_real
  have haverage :
      Real.circleAverage g 0 1 =
        ((2 / Real.pi : ℂ) *
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (((Real.sin (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * f (circleMap 0 1 θ)) := by
    -- Translate the Laurent weight back to the textbook half-angle average.
    calc
      Real.circleAverage g 0 1
        = ((2 * Real.pi)⁻¹ : ℝ) •
            ∫ θ in (0 : ℝ)..(2 * Real.pi), g (circleMap 0 1 θ) := by
              rw [Real.circleAverage_def]
      _ = ((2 * Real.pi)⁻¹ : ℝ) •
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              (4 : ℂ) *
                ((((Real.sin (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * f (circleMap 0 1 θ)) := by
              have hpointwise :
                  (fun θ : ℝ ↦ g (circleMap 0 1 θ)) =
                    fun θ : ℝ ↦
                      (4 : ℂ) *
                        ((((Real.sin (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * f (circleMap 0 1 θ)) := by
                  funext θ
                  dsimp [g]
                  rw [← unit_circle_sin_sq_weight_as_laurent θ]
                  ring
              rw [hpointwise]
      _ = ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (4 : ℂ)) *
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              (((Real.sin (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * f (circleMap 0 1 θ) := by
              rw [intervalIntegral.integral_const_mul]
              simp [mul_assoc]
      _ = ((2 / Real.pi : ℂ) *
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              (((Real.sin (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * f (circleMap 0 1 θ)) := by
              rw [hscalar]
  -- Apply the circle-average/contour bridge and then the normalized Laurent contour formula.
  calc
    ((2 / Real.pi : ℂ) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (((Real.sin (θ / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * f (circleMap 0 1 θ))
      = Real.circleAverage g 0 1 := by
          rw [haverage]
    _ = ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(0, 1), (z - 0)⁻¹ • g z) := by
          rw [Real.circleAverage_eq_circleIntegral one_ne_zero]
    _ = 2 * f 0 - deriv f 0 := by
          simpa [g] using unit_circle_minus_laurent_circle_integral hd
