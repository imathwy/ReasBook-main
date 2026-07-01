import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search tool `lean_leansearch` was unavailable in this environment.
-- The interval-integral notation and `Real.sqrt` API were verified locally.

noncomputable section

open MeasureTheory Metric
open Real
open scoped Real

/-- Helper for Example III.6-extra-1: the square-root term appearing in the quadratic poles. -/
private def quadraticPoleS (a : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 - 1)

/-- Helper for Example III.6-extra-1: the pole of the quadratic kernel inside the unit disc. -/
private def quadraticPoleInner (a : ℝ) : ℂ :=
  ((-a + quadraticPoleS a : ℝ) : ℂ) * Complex.I

/-- Helper for Example III.6-extra-1: the pole of the quadratic kernel outside the unit disc. -/
private def quadraticPoleOuter (a : ℝ) : ℂ :=
  ((-a - quadraticPoleS a : ℝ) : ℂ) * Complex.I

/-- Helper for Example III.6-extra-1: the difference of the two poles is
`2 sqrt(a^2 - 1) i`. -/
private lemma quadratic_pole_difference (a : ℝ) :
    quadraticPoleInner a - quadraticPoleOuter a =
      ((2 * quadraticPoleS a : ℝ) : ℂ) * Complex.I := by
  -- Expand the subtraction and collect the real coefficient of `I`.
  simp only [quadraticPoleInner, quadraticPoleOuter, sub_mul, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_ofNat]
  apply Complex.ext
  · simp
  · simp
    ring

/-- Helper for Example III.6-extra-1: on the unit circle, the quadratic kernel matches
`(a + sin t)⁻¹` after the contour parametrization derivative is inserted. -/
private lemma unit_circle_kernel_eval
    (a t : ℝ) (ha : 1 < a) :
    deriv (circleMap 0 1) t *
        (2 / ((circleMap 0 1 t) ^ 2 + 2 * (a : ℂ) * Complex.I * circleMap 0 1 t - 1)) =
      (((a + Real.sin t)⁻¹ : ℝ) : ℂ) := by
  -- Rewrite the quadratic denominator as `2 (a + sin t)` times the tangent vector to the unit circle.
  let z : ℂ := circleMap 0 1 t
  have hz_ne : z ≠ 0 := by
    dsimp [z]
    simpa using (circleMap_ne_center (c := (0 : ℂ)) (R := (1 : ℝ)) one_ne_zero (θ := t))
  have hsin_pos : 0 < a + Real.sin t := by
    nlinarith [ha, Real.neg_one_le_sin t]
  have hsin_ne : (((a + Real.sin t : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt hsin_pos)
  have hunit :
      z - z⁻¹ = (2 * (Real.sin t : ℂ)) * Complex.I := by
    -- On the unit circle, inversion changes `sin t` to `- sin t` and preserves `cos t`.
    apply Complex.ext
    · dsimp [z]
      simp [circleMap_zero_inv, circleMap_zero_re, Real.cos_neg]
    · dsimp [z]
      simp [circleMap_zero_inv, circleMap_zero_im, Real.sin_neg, Complex.sin_ofReal_re]
      ring_nf
  have hdenom :
      z ^ 2 + 2 * (a : ℂ) * Complex.I * z - 1 =
        (2 * (((a + Real.sin t) : ℝ) : ℂ)) * deriv (circleMap 0 1) t := by
    -- The textbook algebra is the identity
    -- `z² + 2 a i z - 1 = z (z - z⁻¹ + 2 a i) = 2 (a + sin t) z i`.
    calc
      z ^ 2 + 2 * (a : ℂ) * Complex.I * z - 1
        = z ^ 2 + 2 * (a : ℂ) * Complex.I * z - z * z⁻¹ := by
            rw [mul_inv_cancel₀ hz_ne]
      _ = z * (z + 2 * (a : ℂ) * Complex.I - z⁻¹) := by ring
      _ = z * ((z - z⁻¹) + 2 * (a : ℂ) * Complex.I) := by ring
      _ = z * ((2 * (Real.sin t : ℂ)) * Complex.I + 2 * (a : ℂ) * Complex.I) := by
            rw [hunit]
      _ = z * ((2 * (((a + Real.sin t) : ℝ) : ℂ)) * Complex.I) := by
            rw [Complex.ofReal_add, Complex.ofReal_sin]
            ring
      _ = (2 * (((a + Real.sin t) : ℝ) : ℂ)) * deriv (circleMap 0 1) t := by
            rw [deriv_circleMap]
            dsimp [z]
            ring
  have hderiv_ne : deriv (circleMap 0 1) t ≠ 0 := by
    rw [deriv_circleMap]
    dsimp [z]
    exact mul_ne_zero hz_ne Complex.I_ne_zero
  -- Cancel the common derivative factor and the nonzero real scalar.
  rw [hdenom]
  field_simp [hderiv_ne, hsin_ne]
  have hsin_ne' : ((a : ℂ) + Complex.sin t) ≠ 0 := by
    simpa [Complex.ofReal_add, Complex.ofReal_sin] using hsin_ne
  simpa using (mul_inv_cancel₀ hsin_ne').symm

/-- Helper for Example III.6-extra-1: the quadratic denominator splits using the two poles. -/
private lemma quadratic_kernel_factorization (a : ℝ) (ha : 1 < a) (z : ℂ) :
    z ^ 2 + 2 * (a : ℂ) * Complex.I * z - 1 =
      (z - quadraticPoleInner a) * (z - quadraticPoleOuter a) := by
  -- Expand the pole sum and product, then match the monic quadratic coefficients.
  have hsq : quadraticPoleS a ^ 2 = a ^ 2 - 1 := by
    dsimp [quadraticPoleS]
    rw [sq_sqrt]
    nlinarith [ha]
  have hsum :
      quadraticPoleInner a + quadraticPoleOuter a = ((-2 * a : ℝ) : ℂ) * Complex.I := by
    simp [quadraticPoleInner, quadraticPoleOuter]
    ring
  have hprod : quadraticPoleInner a * quadraticPoleOuter a = (-1 : ℂ) := by
    -- The product of the two imaginary poles is `-(a² - s²) = -1`.
    have hmul_real : a ^ 2 - quadraticPoleS a ^ 2 = 1 := by
      nlinarith [hsq]
    have hI : Complex.I * Complex.I = (-1 : ℂ) := by
      simp [Complex.I_sq]
    calc
      quadraticPoleInner a * quadraticPoleOuter a
          = ((quadraticPoleS a : ℂ) ^ 2 - (a : ℂ) ^ 2) := by
              calc
                ((-a + quadraticPoleS a : ℝ) : ℂ) * Complex.I *
                    (((-a - quadraticPoleS a : ℝ) : ℂ) * Complex.I)
                    = (((( -a + quadraticPoleS a) : ℝ) : ℂ) *
                        (((-a - quadraticPoleS a : ℝ) : ℂ)) * (Complex.I * Complex.I)) := by
                          ring
                _ = (((( -a + quadraticPoleS a) : ℝ) : ℂ) *
                      (((-a - quadraticPoleS a : ℝ) : ℂ)) * (-1 : ℂ)) := by
                        rw [hI]
                _ = ((quadraticPoleS a : ℂ) ^ 2 - (a : ℂ) ^ 2) := by
                      push_cast
                      ring
      _ = (-((a ^ 2 - quadraticPoleS a ^ 2 : ℝ) : ℂ)) := by
            push_cast
            ring
      _ = (-1 : ℂ) := by
            rw [show (((a ^ 2 - quadraticPoleS a ^ 2 : ℝ) : ℂ)) = (1 : ℂ) by
              exact_mod_cast hmul_real]
  calc
    z ^ 2 + 2 * (a : ℂ) * Complex.I * z - 1
      = z ^ 2 - (quadraticPoleInner a + quadraticPoleOuter a) * z +
          quadraticPoleInner a * quadraticPoleOuter a := by
            rw [hsum, hprod]
            push_cast
            ring
    _ = (z - quadraticPoleInner a) * (z - quadraticPoleOuter a) := by
          ring

/-- Helper for Example III.6-extra-1: exactly one quadratic pole lies in the open unit disc. -/
private lemma quadratic_poles_unit_disc (a : ℝ) (ha : 1 < a) :
    quadraticPoleInner a ∈ Metric.ball (0 : ℂ) 1 ∧
      quadraticPoleOuter a ∉ Metric.closedBall (0 : ℂ) 1 := by
  -- Keep the estimates in `ℝ`: `s = sqrt(a² - 1)`, so `a - s < 1 < a + s`.
  let s := quadraticPoleS a
  have hsq : s ^ 2 = a ^ 2 - 1 := by
    dsimp [s, quadraticPoleS]
    rw [sq_sqrt]
    nlinarith [ha]
  have hs_nonneg : 0 ≤ s := by
    dsimp [s, quadraticPoleS]
    exact Real.sqrt_nonneg _
  have hs_lt_a : s < a := by
    nlinarith [hsq, ha, hs_nonneg]
  have hinner_lt : a - s < 1 := by
    have hprod : (a - s) * (a + s) = 1 := by
      nlinarith [hsq]
    have haplus_gt : 1 < a + s := by
      nlinarith [ha, hs_nonneg]
    have haminus_pos : 0 < a - s := by
      nlinarith [ha, hs_lt_a]
    nlinarith [hprod, haplus_gt, haminus_pos]
  have houter_gt : 1 < a + s := by
    nlinarith [ha, hs_nonneg]
  have hinner_norm : ‖quadraticPoleInner a‖ = a - s := by
    have hle : -a + s ≤ 0 := by
      linarith
    calc
      ‖quadraticPoleInner a‖ = |(-a + s : ℝ)| := by
        simpa [s, quadraticPoleInner, norm_mul, Complex.norm_I, mul_one, Complex.ofReal_sub,
          Complex.ofReal_neg] using
          (RCLike.norm_ofReal (K := ℂ) (-a + quadraticPoleS a : ℝ))
      _ = -(-a + s) := by
        rw [abs_of_nonpos hle]
      _ = a - s := by
        ring
  have houter_norm : ‖quadraticPoleOuter a‖ = a + s := by
    have hle : -a - s ≤ 0 := by
      linarith
    calc
      ‖quadraticPoleOuter a‖ = |(-a - s : ℝ)| := by
        simpa [s, quadraticPoleOuter, norm_mul, Complex.norm_I, mul_one, Complex.ofReal_add,
          Complex.ofReal_neg] using
          (RCLike.norm_ofReal (K := ℂ) (-a - quadraticPoleS a : ℝ))
      _ = -(-a - s) := by
        rw [abs_of_nonpos hle]
      _ = a + s := by
        ring
  constructor
  · -- The inner pole has norm `a - s`, which is strictly less than `1`.
    have hlt : ‖quadraticPoleInner a‖ < 1 := by
      rw [hinner_norm]
      exact hinner_lt
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hlt
  · -- The outer pole has norm `a + s`, which is strictly greater than `1`.
    intro hz
    have hz_norm : ‖quadraticPoleOuter a‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
    rw [houter_norm] at hz_norm
    linarith

/-- Helper for Example III.6-extra-1: the factored quadratic kernel splits into the difference of
the two basic Cauchy kernels. -/
private lemma quadratic_kernel_partial_fraction
    (a : ℝ) (ha : 1 < a) {z : ℂ}
    (hz₀ : z ≠ quadraticPoleInner a) (hz₁ : z ≠ quadraticPoleOuter a) :
    2 / (z ^ 2 + 2 * (a : ℂ) * Complex.I * z - 1) =
      (2 / (quadraticPoleInner a - quadraticPoleOuter a)) *
        ((z - quadraticPoleInner a)⁻¹ - (z - quadraticPoleOuter a)⁻¹) := by
  -- After factoring the quadratic, this is the standard two-pole partial fraction identity.
  have hs_pos : 0 < quadraticPoleS a := by
    dsimp [quadraticPoleS]
    apply Real.sqrt_pos.mpr
    nlinarith [ha]
  have hdiff_ne : quadraticPoleInner a - quadraticPoleOuter a ≠ 0 := by
    rw [quadratic_pole_difference]
    apply mul_ne_zero
    · exact_mod_cast (show (2 : ℝ) * quadraticPoleS a ≠ 0 by nlinarith [hs_pos])
    · exact Complex.I_ne_zero
  rw [quadratic_kernel_factorization a ha]
  field_simp [sub_ne_zero.mpr hz₀, sub_ne_zero.mpr hz₁, hdiff_ne]
  ring

/-- Helper for Example III.6-extra-1: a simple pole outside the closed unit disc contributes zero
to the unit-circle integral. -/
private lemma circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall {w : ℂ}
    (hw : w ∉ Metric.closedBall (0 : ℂ) 1) :
    ∮ z in C(0, 1), (z - w)⁻¹ = 0 := by
  -- The reciprocal kernel is holomorphic on a neighborhood of the closed unit disc when the pole
  -- lies outside that disc, so the circle integral vanishes.
  have hsub : DiffContOnCl ℂ (fun z : ℂ ↦ z - w) (Metric.ball (0 : ℂ) (1 : ℝ)) := by
    simpa using (differentiable_id.sub_const w).diffContOnCl
  have hsub_ne :
      ∀ z ∈ closure (Metric.ball (0 : ℂ) (1 : ℝ)), z - w ≠ 0 := by
    intro z hz hzw
    apply hw
    have hz_closed : z ∈ Metric.closedBall (0 : ℂ) (1 : ℝ) :=
      closure_ball_subset_closedBall hz
    simpa [sub_eq_zero.mp hzw] using hz_closed
  have hinv : DiffContOnCl ℂ (fun z : ℂ ↦ (z - w)⁻¹) (Metric.ball (0 : ℂ) (1 : ℝ)) :=
    hsub.inv hsub_ne
  simpa using (DiffContOnCl.circleIntegral_eq_zero (h0 := by norm_num) hinv)

/-- Helper for Example III.6-extra-1: the unit-circle contour integral of the quadratic kernel is
the contribution of the unique pole inside the disc. -/
private lemma circleIntegral_quadratic_kernel
    (a : ℝ) (ha : 1 < a) :
    ∮ z in C(0, 1), 2 / (z ^ 2 + 2 * (a : ℂ) * Complex.I * z - 1) =
      (((2 * π / quadraticPoleS a : ℝ)) : ℂ) := by
  -- Route correction: evaluate the contour integral by an explicit partial-fraction split rather
  -- than by a broad holomorphic-vanishing search.
  rcases quadratic_poles_unit_disc a ha with ⟨hz₀_mem, hz₁_out⟩
  have hz₀_not_sphere : quadraticPoleInner a ∉ Metric.sphere (0 : ℂ) 1 := by
    intro hz
    have hz_norm : ‖quadraticPoleInner a‖ = 1 := by
      simpa [sub_zero] using mem_sphere_iff_norm.mp hz
    have hz_lt : ‖quadraticPoleInner a‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hz₀_mem
    linarith
  have hz₁_not_sphere : quadraticPoleOuter a ∉ Metric.sphere (0 : ℂ) 1 := by
    intro hz
    apply hz₁_out
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_of_eq (by simpa [sub_zero] using mem_sphere_iff_norm.mp hz)
  have hCI₀ : CircleIntegrable (fun z : ℂ ↦ (z - quadraticPoleInner a)⁻¹) 0 1 := by
    rw [circleIntegrable_sub_inv_iff]
    right
    simpa using hz₀_not_sphere
  have hCI₁ : CircleIntegrable (fun z : ℂ ↦ (z - quadraticPoleOuter a)⁻¹) 0 1 := by
    rw [circleIntegrable_sub_inv_iff]
    right
    simpa using hz₁_not_sphere
  have hrewrite :
      ∮ z in C(0, 1), 2 / (z ^ 2 + 2 * (a : ℂ) * Complex.I * z - 1) =
        ∮ z in C(0, 1),
          (2 / (quadraticPoleInner a - quadraticPoleOuter a)) *
            ((z - quadraticPoleInner a)⁻¹ - (z - quadraticPoleOuter a)⁻¹) := by
    -- On the unit circle, the partial fraction identity applies pointwise because neither pole lies
    -- on the contour.
    refine circleIntegral.integral_congr (by norm_num) ?_
    intro z hz
    have hz_closed : z ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_of_eq (by simpa [sub_zero] using mem_sphere_iff_norm.mp hz)
    have hz₀_ne : z ≠ quadraticPoleInner a := by
      intro h
      exact hz₀_not_sphere (h ▸ hz)
    have hz₁_ne : z ≠ quadraticPoleOuter a := by
      intro h
      exact hz₁_out (h ▸ hz_closed)
    exact quadratic_kernel_partial_fraction a ha hz₀_ne hz₁_ne
  have hs_pos : 0 < quadraticPoleS a := by
    dsimp [quadraticPoleS]
    apply Real.sqrt_pos.mpr
    nlinarith [ha]
  have hs_ne : (((quadraticPoleS a : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt hs_pos)
  calc
    ∮ z in C(0, 1), 2 / (z ^ 2 + 2 * (a : ℂ) * Complex.I * z - 1)
      = ∮ z in C(0, 1),
          (2 / (quadraticPoleInner a - quadraticPoleOuter a)) *
            ((z - quadraticPoleInner a)⁻¹ - (z - quadraticPoleOuter a)⁻¹) := hrewrite
    _ = (2 / (quadraticPoleInner a - quadraticPoleOuter a)) *
          ((∮ z in C(0, 1), (z - quadraticPoleInner a)⁻¹) -
            ∮ z in C(0, 1), (z - quadraticPoleOuter a)⁻¹) := by
          rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub hCI₀ hCI₁]
    _ = (2 / (quadraticPoleInner a - quadraticPoleOuter a)) * (2 * π * Complex.I) := by
          rw [circleIntegral.integral_sub_inv_of_mem_ball hz₀_mem,
            circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall hz₁_out, sub_zero]
    _ = (((2 * π / quadraticPoleS a : ℝ)) : ℂ) := by
          rw [quadratic_pole_difference]
          have hs2_ne : (((2 * quadraticPoleS a : ℝ) : ℂ)) ≠ 0 := by
            exact_mod_cast (show (2 : ℝ) * quadraticPoleS a ≠ 0 by nlinarith [hs_pos])
          field_simp [hs2_ne, hs_ne]
          norm_num
          field_simp [hs_ne]
          ring

/-- Example III.6-extra-1: if `a > 1`, then
`∫_0^{2π} dt / (a + sin t) = 2π / sqrt (a^2 - 1)`. -/
theorem integral_inv_add_sin
    (a : ℝ) (ha : 1 < a) :
    ∫ t in (0 : ℝ)..(2 * π), (a + sin t)⁻¹ = 2 * π / sqrt (a ^ 2 - 1) := by
  -- Rewrite the real interval integral as the unit-circle contour integral of the quadratic kernel.
  have hcont :
      Continuous fun t : ℝ ↦ (a + Real.sin t)⁻¹ := by
    refine (continuous_const.add Real.continuous_sin).inv₀ ?_
    intro t
    change a + Real.sin t ≠ 0
    have hs : -1 ≤ Real.sin t := Real.neg_one_le_sin t
    exact ne_of_gt <| by linarith
  have hInt :
      IntervalIntegrable (fun t : ℝ ↦ (a + Real.sin t)⁻¹) volume 0 (2 * π) :=
    hcont.intervalIntegrable 0 (2 * π)
  have hcast :
      (∫ t in (0 : ℝ)..(2 * π), (((a + Real.sin t)⁻¹ : ℝ) : ℂ)) =
        (((∫ t in (0 : ℝ)..(2 * π), (a + Real.sin t)⁻¹ : ℝ)) : ℂ) := by
    simpa using
      (Complex.ofRealCLM.intervalIntegral_comp_comm
        (a := (0 : ℝ)) (b := (2 * π)) (f := fun t : ℝ ↦ (a + Real.sin t)⁻¹) hInt)
  have hcircle_to_real :
      ∮ z in C(0, 1), 2 / (z ^ 2 + 2 * (a : ℂ) * Complex.I * z - 1) =
        (((∫ t in (0 : ℝ)..(2 * π), (a + Real.sin t)⁻¹ : ℝ)) : ℂ) := by
    calc
      ∮ z in C(0, 1), 2 / (z ^ 2 + 2 * (a : ℂ) * Complex.I * z - 1)
        = ∫ t in (0 : ℝ)..(2 * π),
            deriv (circleMap 0 1) t *
              (2 / ((circleMap 0 1 t) ^ 2 + 2 * (a : ℂ) * Complex.I * circleMap 0 1 t - 1)) := by
              rw [circleIntegral]
              simp [smul_eq_mul]
      _ = ∫ t in (0 : ℝ)..(2 * π), (((a + Real.sin t)⁻¹ : ℝ) : ℂ) := by
            refine intervalIntegral.integral_congr_ae ?_
            filter_upwards with t ht
            simpa using unit_circle_kernel_eval a t ha
      _ = (((∫ t in (0 : ℝ)..(2 * π), (a + Real.sin t)⁻¹ : ℝ)) : ℂ) := hcast
  -- Evaluate the contour integral and transport the equality back to `ℝ`.
  apply Complex.ofReal_inj.mp
  calc
    (((∫ t in (0 : ℝ)..(2 * π), (a + Real.sin t)⁻¹ : ℝ)) : ℂ)
      = ∮ z in C(0, 1), 2 / (z ^ 2 + 2 * (a : ℂ) * Complex.I * z - 1) := by
          exact hcircle_to_real.symm
    _ = (((2 * π / quadraticPoleS a : ℝ)) : ℂ) := circleIntegral_quadratic_kernel a ha
    _ = ((2 * π / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ) := by
          simp [quadraticPoleS]
