import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open FormalMultilinearSeries

/-- The shifted scalar series for `(1 - I * x)⁻¹` about the center `x₀`. -/
abbrev shiftedGeometricInverseSeries (x₀ : ℝ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  ofScalars ℂ (fun n ↦ Complex.I ^ n / ((1 : ℂ) - Complex.I * (x₀ : ℂ)) ^ (n + 1))

/-- Helper for Remark 1: the denominator `1 - I * x₀` has the textbook modulus
`sqrt (1 + x₀^2)`. -/
lemma one_sub_I_mul_ofReal_norm (x₀ : ℝ) :
    ‖(1 : ℂ) - Complex.I * (x₀ : ℂ)‖ = Real.sqrt (1 + x₀ ^ 2) := by
  -- Compare squares so the norm computation reduces to `Complex.normSq_apply`.
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), Complex.sq_norm, Real.sq_sqrt]
  · simp [Complex.normSq_apply, pow_two]
  · nlinarith

/-- Helper for Remark 1: the shifted geometric denominator never vanishes for real `x₀`. -/
lemma one_sub_I_mul_ofReal_ne_zero (x₀ : ℝ) :
    ((1 : ℂ) - Complex.I * (x₀ : ℂ)) ≠ 0 := by
  -- The norm formula above shows the modulus is strictly positive.
  apply norm_ne_zero_iff.mp
  rw [one_sub_I_mul_ofReal_norm]
  exact Real.sqrt_ne_zero'.2 (by nlinarith)

/-- Helper for Remark 1: consecutive coefficient norms differ by the constant factor
`‖1 - I*x₀‖`. -/
lemma shifted_geometric_inverse_coeff_norm_ratio (x₀ : ℝ) (n : ℕ) :
    ‖Complex.I ^ n / ((1 : ℂ) - Complex.I * (x₀ : ℂ)) ^ (n + 1)‖ /
      ‖Complex.I ^ (n + 1) / ((1 : ℂ) - Complex.I * (x₀ : ℂ)) ^ (n + 2)‖ =
      ‖(1 : ℂ) - Complex.I * (x₀ : ℂ)‖₊ := by
  have hna : (‖(1 : ℂ) - Complex.I * (x₀ : ℂ)‖ : ℝ) ≠ 0 :=
    norm_ne_zero_iff.mpr (one_sub_I_mul_ofReal_ne_zero x₀)
  have hratio :
      (‖(1 : ℂ) - Complex.I * (x₀ : ℂ)‖ ^ (n + 1))⁻¹ *
        ‖(1 : ℂ) - Complex.I * (x₀ : ℂ)‖ ^ (n + 2) =
        ‖(1 : ℂ) - Complex.I * (x₀ : ℂ)‖ := by
    -- The remaining real identity is a one-line cancellation of powers of `‖1 - I*x₀‖`.
    field_simp [pow_ne_zero (n + 1) hna]
    ring
  -- Reinsert the normalized complex coefficients into the real ratio identity.
  simpa [Complex.norm_I, one_sub_I_mul_ofReal_ne_zero x₀] using hratio

/-- The shifted geometric inverse series at `x₀` has radius the modulus of `1 - I * x₀`. -/
-- Proof sketch: apply `FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto` to
-- `shiftedGeometricInverseSeries x₀`; its coefficient norms have constant inverse ratio
-- `‖c n‖ / ‖c (n + 1)‖ = ‖1 - I * x₀‖`.
theorem shifted_geometric_series_radius (x₀ : ℝ) :
    (shiftedGeometricInverseSeries x₀).radius =
      ‖(1 : ℂ) - Complex.I * (x₀ : ℂ)‖₊ := by
  have hr : ‖(1 : ℂ) - Complex.I * (x₀ : ℂ)‖₊ ≠ 0 := by
    simpa using (nnnorm_ne_zero_iff.mpr (one_sub_I_mul_ofReal_ne_zero x₀))
  have hconst :
      (fun n ↦ ‖Complex.I ^ n / ((1 : ℂ) - Complex.I * (x₀ : ℂ)) ^ (n + 1)‖ /
        ‖Complex.I ^ (n + 1) / ((1 : ℂ) - Complex.I * (x₀ : ℂ)) ^ (n + 2)‖) =
        fun _ : ℕ ↦ (‖(1 : ℂ) - Complex.I * (x₀ : ℂ)‖₊ : ℝ) := by
    funext n
    exact shifted_geometric_inverse_coeff_norm_ratio x₀ n
  -- The ratio test applies because the norm ratio is exactly constant.
  simpa [shiftedGeometricInverseSeries] using
    (FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto (𝕜 := ℂ) (E := ℂ)
      (c := fun n ↦ Complex.I ^ n / ((1 : ℂ) - Complex.I * (x₀ : ℂ)) ^ (n + 1))
      (r := ‖(1 : ℂ) - Complex.I * (x₀ : ℂ)‖₊) hr <| by rw [hconst]; exact tendsto_const_nhds)

/-- Helper for Remark 1: after substituting `x ↦ I * x`, the scalar geometric coefficients become
exactly the shifted coefficients from the remark. -/
lemma recentered_geometric_coeff (x₀ : ℝ) (n : ℕ) :
    ((FormalMultilinearSeries.ofScalars ℂ
      (fun k ↦ (((1 : ℂ) - Complex.I * (x₀ : ℂ)) ^ (k + 1))⁻¹)).compContinuousLinearMap
        (Complex.I • ContinuousLinearMap.id ℂ ℂ)).coeff n =
      Complex.I ^ n / (((1 : ℂ) - Complex.I * (x₀ : ℂ)) ^ (n + 1)) := by
  -- Evaluating on the all-ones vector turns the multilinear coefficient into a scalar coefficient.
  rw [FormalMultilinearSeries.coeff, FormalMultilinearSeries.compContinuousLinearMap_apply]
  simp [FormalMultilinearSeries.ofScalars, List.prod_ofFn, div_eq_mul_inv, mul_comm]

/-- Helper for Remark 1: composing the geometric series with multiplication by `I` produces the
shifted inverse series. -/
lemma shifted_geometric_inverse_series_eq_recentered_geometric (x₀ : ℝ) :
    (FormalMultilinearSeries.ofScalars ℂ
      (fun n ↦ (((1 : ℂ) - Complex.I * (x₀ : ℂ)) ^ (n + 1))⁻¹)).compContinuousLinearMap
        (Complex.I • ContinuousLinearMap.id ℂ ℂ) =
      shiftedGeometricInverseSeries x₀ := by
  -- Equality of scalar formal series is equality of their coefficients.
  ext n
  simpa [shiftedGeometricInverseSeries] using recentered_geometric_coeff x₀ n

/-- Remark 1: the expansion of `(1 - I * x)⁻¹` around the real center `x₀` converges on the ball
of radius `sqrt (1 + x₀^2)`, giving an example whose shifted convergence radius exceeds
`1 - |x₀|`. -/
-- Proof sketch: start from `Complex.one_div_sub_hasFPowerSeriesOnBall_zero` with
-- `z = 1 - I * x₀`, precompose by the linear isometry `x ↦ I * x`, shift the center by `x₀`
-- using `HasFPowerSeriesOnBall.comp_sub`, and simplify the coefficients to
-- `shiftedGeometricInverseSeries x₀`. The radius is `‖1 - I * x₀‖ = sqrt (1 + x₀^2)`.
theorem shifted_geometric_inverse_hasFPowerSeriesOnBall (x₀ : ℝ) :
    HasFPowerSeriesOnBall
      (fun x : ℂ ↦ ((1 : ℂ) - Complex.I * x)⁻¹)
      (shiftedGeometricInverseSeries x₀)
      (x₀ : ℂ)
      (ENNReal.ofReal (Real.sqrt (1 + x₀ ^ 2))) := by
  let a : ℂ := (1 : ℂ) - Complex.I * (x₀ : ℂ)
  let u : ℂ →ₗᵢ[ℂ] ℂ :=
    { toLinearMap := Complex.I • LinearMap.id
      norm_map' := by
        intro z
        simp }
  have hgeom :
      HasFPowerSeriesOnBall (fun x : ℂ ↦ 1 / (a - x))
        (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ (a ^ (n + 1))⁻¹)) 0 ‖a‖ₑ :=
    Complex.one_div_sub_hasFPowerSeriesOnBall_zero (z := a) (by
      simpa [a] using one_sub_I_mul_ofReal_ne_zero x₀)
  have hgeom' :
      HasFPowerSeriesOnBall (fun x : ℂ ↦ 1 / (a - x))
        (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ (a ^ (n + 1))⁻¹))
        (u.toContinuousLinearMap 0) ‖a‖ₑ := by
    simpa using hgeom
  -- First substitute `x ↦ I * x`, then shift the center from `0` to `x₀`.
  have hcomp := hgeom'.compContinuousLinearMap (u := u.toContinuousLinearMap) (x := (0 : ℂ))
  have hshift := hcomp.comp_sub (x₀ : ℂ)
  have hseries :
      (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ (a ^ (n + 1))⁻¹)).compContinuousLinearMap
          u.toContinuousLinearMap = shiftedGeometricInverseSeries x₀ := by
    simpa [a, u] using shifted_geometric_inverse_series_eq_recentered_geometric x₀
  rw [hseries] at hshift
  have hfun :
      Set.EqOn (fun z : ℂ ↦ ((fun x : ℂ ↦ 1 / (a - x)) ∘ u.toContinuousLinearMap) (z - (x₀ : ℂ)))
        (fun x : ℂ ↦ ((1 : ℂ) - Complex.I * x)⁻¹)
        (Metric.eball (0 + (x₀ : ℂ)) (‖a‖ₑ / ‖u.toContinuousLinearMap‖ₑ)) := by
    -- This is the algebraic normalization of the textbook identity
    -- `(1 - I*x₀) - I*(z - x₀) = 1 - I*z`.
    intro z hz
    simp [Function.comp, a, u, sub_eq_add_neg, mul_add]
  have hradius : ‖(1 : ℂ) - Complex.I * (x₀ : ℂ)‖ₑ = ENNReal.ofReal (Real.sqrt (1 + x₀ ^ 2)) := by
    -- Convert the ENNReal radius back to the real norm computed above.
    rw [← one_sub_I_mul_ofReal_norm x₀, ofReal_norm]
  have hfinal := hshift.congr hfun
  simpa [a, u, hradius] using hfinal

/-- The shifted convergence radius is strictly larger than the naive bound `1 - |x₀|` away
from the original center. -/
-- Proof sketch: rewrite the radius as `sqrt (1 + x₀^2)` and compare it to `1 - |x₀|` by
-- elementary real inequalities.
theorem shifted_geometric_radius_gt_naive_bound (x₀ : ℝ) (hx₀ : x₀ ≠ 0) :
    1 - |x₀| < Real.sqrt (1 + x₀ ^ 2) := by
  -- The strict form is false at `x₀ = 0`; the source example is genuinely strict for
  -- nonzero recentering parameters.
  have h_abs_pos : 0 < |x₀| := by
    -- Nonzero recentering gives the only strict input on the left-hand side.
    exact abs_pos.mpr hx₀
  have h_left : 1 - |x₀| < 1 := by
    -- Compare to `1` by discarding the positive quantity `|x₀|`.
    nlinarith
  have h_right : 1 ≤ Real.sqrt (1 + x₀ ^ 2) := by
    have h_sq_nonneg : 0 ≤ 1 + x₀ ^ 2 := by
      -- The square term keeps the radicand at least `1`.
      nlinarith [sq_nonneg x₀]
    have h_sqrt_sq : (Real.sqrt (1 + x₀ ^ 2)) ^ 2 = 1 + x₀ ^ 2 := by
      -- Rewrite the square of the square root back to the radicand.
      rw [Real.sq_sqrt h_sq_nonneg]
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (1 + x₀ ^ 2) := by
      -- This is the nonnegativity side condition for comparing squares.
      exact Real.sqrt_nonneg (1 + x₀ ^ 2)
    nlinarith [sq_nonneg x₀, h_sqrt_sq, h_sqrt_nonneg]
  -- The source comparison now factors through the intermediate value `1`.
  exact lt_of_lt_of_le h_left h_right
