import Mathlib

-- Semantic recall note: the proof follows the source route through the reflected-circle identity
-- from Chapter II, then computes the resulting ordinary circle integrals by Cauchy's formula.

open scoped Topology ComplexConjugate
open Complex

noncomputable section

section

variable {f : ℂ → ℂ}
variable (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))

/-- Helper for Exercise 3: complex conjugation commutes with interval integrals of complex-valued
functions. -/
lemma conj_intervalIntegral {g : ℝ → ℂ} {a b : ℝ} :
    conj (∫ t in a..b, g t) = ∫ t in a..b, conj (g t) := by
  -- Expand the interval integral into the difference of two set integrals, then conjugate each
  -- term.
  simp [intervalIntegral, integral_conj, map_sub]

/-- Helper for Exercise 3: on the unit circle, complex conjugation is inversion. -/
lemma unit_circle_conj_eq_inv (θ : ℝ) :
    conj (circleMap 0 1 θ) = (circleMap 0 1 θ)⁻¹ := by
  -- This is the standard `|z| = 1` identity specialized to the circle parametrization.
  simpa [circleMap_zero_inv] using conj_circleMap_zero 1 θ

/-- Helper for Exercise 3: conjugating the unit-circle integrand contributes the factor `-z⁻²`. -/
lemma unit_circle_conj_integrand (g : ℂ → ℂ) (θ : ℝ) :
    conj (deriv (circleMap 0 1) θ * g (circleMap 0 1 θ)) =
      -(deriv (circleMap 0 1) θ *
        (conj (g (circleMap 0 1 θ)) / (circleMap 0 1 θ) ^ (2 : ℕ))) := by
  -- The tangent vector conjugates to its negative times `z⁻²`, and the remaining algebra is
  -- purely commutative.
  have hz : circleMap 0 1 θ ≠ 0 := by
    exact circleMap_ne_center (c := 0) (R := 1) (θ := θ) (one_ne_zero : (1 : ℝ) ≠ 0)
  have hunit : conj (circleMap 0 1 θ) = (circleMap 0 1 θ)⁻¹ := unit_circle_conj_eq_inv θ
  have hderiv :
      conj (deriv (circleMap 0 1) θ) =
        -(deriv (circleMap 0 1) θ / (circleMap 0 1 θ) ^ (2 : ℕ)) := by
    rw [deriv_circleMap, map_mul, Complex.conj_I, hunit]
    simp [div_eq_mul_inv, pow_two, hz, mul_assoc, mul_comm]
  calc
    conj (deriv (circleMap 0 1) θ * g (circleMap 0 1 θ)) =
        conj (deriv (circleMap 0 1) θ) * conj (g (circleMap 0 1 θ)) := by
      simp
    _ =
        (-(deriv (circleMap 0 1) θ / (circleMap 0 1 θ) ^ (2 : ℕ))) *
          conj (g (circleMap 0 1 θ)) := by
      rw [hderiv]
    _ =
        -(deriv (circleMap 0 1) θ *
          (conj (g (circleMap 0 1 θ)) / (circleMap 0 1 θ) ^ (2 : ℕ))) := by
      simp [div_eq_mul_inv, mul_assoc, mul_comm]

/-- Helper for Exercise 3: on the positively oriented unit circle, conjugating the circle integral
of `g` produces the integral of `-conj (g z) / z²`. -/
theorem conj_circleIntegral_unitCircle_eq_neg_circleIntegral_conj_div_zsq
    {g : ℂ → ℂ} (hg : ContinuousOn g (Metric.sphere (0 : ℂ) 1)) :
    conj (∮ z in C(0, 1), g z) =
      -(∮ z in C(0, 1), conj (g z) / z ^ (2 : ℕ)) := by
  let _ := hg
  -- Expand the circle integral into its interval parametrization and rewrite the integrand
  -- pointwise using the reflected tangent-vector identity.
  calc
    conj (∮ z in C(0, 1), g z) =
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          conj (deriv (circleMap 0 1) θ • g (circleMap 0 1 θ)) := by
      rw [circleIntegral, conj_intervalIntegral]
    _ =
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          -(deriv (circleMap 0 1) θ •
            (conj (g (circleMap 0 1 θ)) / (circleMap 0 1 θ) ^ (2 : ℕ))) := by
      refine intervalIntegral.integral_congr ?_
      intro θ hθ
      simpa [smul_eq_mul] using unit_circle_conj_integrand g θ
    _ =
        -∫ θ in (0 : ℝ)..2 * Real.pi,
          deriv (circleMap 0 1) θ • (conj (g (circleMap 0 1 θ)) / (circleMap 0 1 θ) ^ (2 : ℕ)) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∮ z in C(0, 1), conj (g z) / z ^ (2 : ℕ)) := by
      rfl

/-- Helper for Exercise 3: analyticity on a neighborhood of the closed unit disc packages as the
standard `DiffContOnCl` owner on the open unit disc. -/
lemma analyticOnNhd_diffContOnCl_unitDisc
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) :
    DiffContOnCl ℂ f (Metric.ball (0 : ℂ) 1) := by
  -- We first restrict analyticity to differentiability on the closed unit disc, then convert that
  -- closed-disc owner into the Cauchy-integral `DiffContOnCl` package on the open disc.
  exact (hf.analyticOn.differentiableOn).diffContOnCl_ball subset_rfl

/-- Helper for Exercise 3: on the unit circle, the reflected auxiliary kernel is exactly the target
integrand from the exercise. -/
lemma unit_circle_conj_cauchy_aux_integrand
    {a z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) 1) :
    conj (f z / (z * (1 - conj a * z))) / z ^ (2 : ℕ) = conj (f z) / (z - a) := by
  -- On `|z| = 1`, conjugation turns `z` into `z⁻¹`, so the conjugated denominator collapses to
  -- `z - a` after multiplying by `z²`.
  have hz_norm : ‖z‖ = 1 := by
    simpa using mem_sphere_iff_norm.1 hz
  have hz0 : z ≠ 0 := by
    intro hz0
    simpa [hz0] using hz_norm
  have hz_conj : conj z = z⁻¹ := by
    simpa using (RCLike.inv_eq_conj hz_norm).symm
  calc
    conj (f z / (z * (1 - conj a * z))) / z ^ (2 : ℕ) =
        conj (f z) / (conj (z * (1 - conj a * z)) * z ^ (2 : ℕ)) := by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ = conj (f z) / (z - a) := by
      rw [map_mul, map_sub, map_one, map_mul, conj_conj, hz_conj]
      field_simp [hz0]

/-- Helper for Exercise 3: away from `0` and the second pole, the inside-disc kernel splits into a
simple pole at `0` plus a holomorphic remainder. -/
lemma reciprocal_split_unit_circle_kernel_of_norm_lt_one
    {a z : ℂ}
    (hz : z ≠ 0)
    (hden : 1 - conj a * z ≠ 0) :
    1 / (z * (1 - conj a * z)) = 1 / z + conj a / (1 - conj a * z) := by
  have hden' : 1 - z * conj a ≠ 0 := by
    simpa [mul_comm] using hden
  -- Clear denominators against the common product `z * (1 - conj a * z)`.
  field_simp [hz, hden, hden']
  ring_nf

/-- Helper for Exercise 3: if `‖a‖ < 1`, then the factor `1 - conj a * z` never vanishes on the
closed unit disc. -/
lemma one_sub_conj_mul_ne_zero_on_closed_unitDisc
    {a z : ℂ}
    (ha : ‖a‖ < 1)
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    1 - conj a * z ≠ 0 := by
  -- A vanishing denominator would force `‖conj a * z‖ = 1`, contradicting `‖a‖ < 1`.
  intro hzero
  have hz_norm : ‖z‖ ≤ 1 := by
    simpa using mem_closedBall_iff_norm.1 hz
  have hbound : ‖conj a * z‖ ≤ ‖a‖ := by
    calc
      ‖conj a * z‖ = ‖a‖ * ‖z‖ := by rw [norm_mul, norm_conj]
      _ ≤ ‖a‖ * 1 := by
        exact mul_le_mul_of_nonneg_left hz_norm (norm_nonneg _)
      _ = ‖a‖ := by ring
  have hone_le : (1 : ℝ) ≤ ‖a‖ := by
    calc
      1 = ‖conj a * z‖ := by
        have hmul : conj a * z = 1 := (sub_eq_zero.mp hzero).symm
        simpa [hmul]
      _ ≤ ‖a‖ := hbound
  exact (not_le_of_gt ha) hone_le

/-- Helper for Exercise 3: away from `0` and the exterior pole, the outside-disc kernel splits as
the difference of the two standard Cauchy kernels at `0` and `1 / conj a`. -/
lemma reciprocal_split_unit_circle_kernel_of_one_lt_norm
    {a z : ℂ}
    (ha0 : a ≠ 0)
    (hz : z ≠ 0)
    (hzb : z ≠ 1 / conj a) :
    1 / (z * (1 - conj a * z)) = 1 / z - 1 / (z - 1 / conj a) := by
  have hcona : conj a ≠ 0 := by
    intro hcona
    apply ha0
    simpa using congrArg conj hcona
  have hden : 1 - z * conj a ≠ 0 := by
    intro hzero
    apply hzb
    have hmul : z * conj a = 1 := (sub_eq_zero.mp hzero).symm
    have hinv_mul := congrArg (fun t : ℂ => t * (conj a)⁻¹) hmul
    simpa [hcona, mul_assoc, one_div] using hinv_mul
  have hfactor : 1 - conj a * z = -(conj a) * (z - 1 / conj a) := by
    field_simp [hcona]
    ring
  -- Rewrite the reflected denominator as the product that matches the two Cauchy kernels.
  calc
    1 / (z * (1 - conj a * z)) = 1 / (-(conj a) * (z * (z - 1 / conj a))) := by
      rw [hfactor]
      ring
    _ = -(1 / conj a) / (z * (z - 1 / conj a)) := by
      field_simp [hz, hzb, hcona]
    _ = 1 / z - 1 / (z - 1 / conj a) := by
      have hden' : conj a * z - 1 ≠ 0 := by
        intro hzero
        apply hden
        have hneg := congrArg Neg.neg hzero
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm] using hneg
      field_simp [hz, hzb, hcona, hden']
      ring_nf

/-- Helper for Exercise 3: if `‖a‖ > 1`, then the second pole `1 / conj a` lies inside the open
unit disc. -/
lemma inv_conj_mem_unit_ball_of_one_lt_norm
    {a : ℂ}
    (ha : 1 < ‖a‖) :
    1 / conj a ∈ Metric.ball (0 : ℂ) 1 := by
  -- The reflected pole has norm `‖a‖⁻¹`, so it lies strictly inside the unit disc.
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  calc
    ‖1 / conj a‖ = ‖a‖⁻¹ := by simp [norm_div, norm_conj]
    _ < 1 := inv_lt_one_of_one_lt₀ ha

/-- Helper for Exercise 3: the reflected-circle identity converts the normalized target integral
into the conjugate of the normalized auxiliary kernel integral. -/
lemma unit_circle_conj_reflected_aux_normalized
    {a : ℂ}
    (hg : ContinuousOn (fun z : ℂ ↦ f z / (z * (1 - conj a * z))) (Metric.sphere (0 : ℂ) 1)) :
    ((2 * Real.pi * I : ℂ)⁻¹) •
        (∮ z in C(0, (1 : ℝ)), conj (f z) / (z - a)) =
      conj (((2 * Real.pi * I : ℂ)⁻¹) •
        (∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z)))) := by
  let c : ℂ := ((2 * Real.pi * I : ℂ)⁻¹)
  have hreflect :
      conj (∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z))) =
        -(∮ z in C(0, (1 : ℝ)), conj (f z) / (z - a)) := by
    -- First rewrite the conjugated auxiliary contour integral using the reflected-circle formula.
    calc
      conj (∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z))) =
          -(∮ z in C(0, (1 : ℝ)),
            conj (f z / (z * (1 - conj a * z))) / z ^ (2 : ℕ)) := by
        simpa using
          conj_circleIntegral_unitCircle_eq_neg_circleIntegral_conj_div_zsq
            (g := fun z : ℂ ↦ f z / (z * (1 - conj a * z))) hg
      _ = -(∮ z in C(0, (1 : ℝ)), conj (f z) / (z - a)) := by
        congr 1
        refine circleIntegral.integral_congr (show (0 : ℝ) ≤ 1 by norm_num) ?_
        intro z hz
        simpa using unit_circle_conj_cauchy_aux_integrand (f := f) (a := a) hz
  have hc : conj c = -c := by
    change conj (((2 * Real.pi * I : ℂ)⁻¹)) = -(((2 * Real.pi * I : ℂ)⁻¹))
    have htwo : conj (2 : ℂ) = (2 : ℂ) := by
      simpa using (Complex.conj_ofReal (2 : ℝ))
    have hbase : conj (2 * Real.pi * I : ℂ) = -(2 * Real.pi * I) := by
      calc
        conj (2 * Real.pi * I : ℂ) = conj (2 : ℂ) * conj (Real.pi : ℂ) * conj I := by
          simp [mul_assoc]
        _ = -(2 * Real.pi * I) := by
          simp [htwo, Complex.conj_I, mul_assoc]
    rw [show conj (((2 * Real.pi * I : ℂ)⁻¹)) = (conj (2 * Real.pi * I : ℂ))⁻¹ by simp, hbase]
    simp
  have hnormalized :
      conj (c • ∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z))) =
        c • ∮ z in C(0, (1 : ℝ)), conj (f z) / (z - a) := by
    -- Conjugating the normalization scalar cancels the minus sign from the reflected contour.
    calc
      conj (c • ∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z))) =
          conj c *
            conj (∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z))) := by
        simp [c, smul_eq_mul]
      _ = (-c) * (-(∮ z in C(0, (1 : ℝ)), conj (f z) / (z - a))) := by
        rw [hc, hreflect]
      _ = c • ∮ z in C(0, (1 : ℝ)), conj (f z) / (z - a) := by
        simpa [smul_eq_mul]
  simpa [c, eq_comm] using hnormalized

include hf

/-- Exercise 3 (1): if `f` is holomorphic on a neighborhood of the closed unit disc, then the
unit-circle Cauchy integral of `conj ∘ f` equals `conj (f 0)` for `‖a‖ < 1`. -/
theorem unit_circle_conj_cauchy_integral_eq_conj_zero_of_norm_lt_one
    {a : ℂ}
    (ha : ‖a‖ < 1) :
    ((2 * Real.pi * I : ℂ)⁻¹) •
        (∮ z in C(0, (1 : ℝ)), conj (f z) / (z - a)) =
      conj (f 0) := by
  have hd : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) 1) :=
    analyticOnNhd_diffContOnCl_unitDisc (f := f) hf
  let hAux : ℂ → ℂ := fun z ↦ f z / (1 - conj a * z)
  have hAux_diff : DiffContOnCl ℂ hAux (Metric.ball (0 : ℂ) 1) := by
    have hden_dc : DiffContOnCl ℂ (fun z : ℂ ↦ 1 - conj a * z) (Metric.ball (0 : ℂ) 1) := by
      -- The reflected denominator is an entire affine function.
      have hden_diff : Differentiable ℂ (fun z : ℂ ↦ 1 - conj a * z) := by
        intro z
        have hmul : DifferentiableAt ℂ (fun w : ℂ ↦ conj a * w) z := by
          simpa [mul_comm] using
            (differentiableAt_id (𝕜 := ℂ) (x := z)).const_mul (conj a)
        simpa using (differentiableAt_const (𝕜 := ℂ) (c := (1 : ℂ))).sub hmul
      exact hden_diff.diffContOnCl
    have hden_inv : DiffContOnCl ℂ (fun z : ℂ ↦ (1 - conj a * z)⁻¹) (Metric.ball (0 : ℂ) 1) := by
      -- Inverting is legitimate because the reflected factor never vanishes on the closed disc.
      refine hden_dc.inv ?_
      intro z hz
      have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 := by
        simpa [closure_ball (0 : ℂ) (show (1 : ℝ) ≠ 0 by norm_num)] using hz
      exact one_sub_conj_mul_ne_zero_on_closed_unitDisc (a := a) (z := z) ha hz'
    -- Multiply the original holomorphic function by the inverted reflected factor.
    simpa [hAux, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      hden_inv.smul hd
  have hcont_f : ContinuousOn f (Metric.sphere (0 : ℂ) 1) :=
    (hd.continuousOn_ball).mono Metric.sphere_subset_closedBall
  have hcont_den :
      ContinuousOn (fun z : ℂ ↦ z * (1 - conj a * z)) (Metric.sphere (0 : ℂ) 1) := by
    -- The reflected denominator is polynomial, hence continuous on the boundary circle.
    exact continuousOn_id.mul (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
  have hg :
      ContinuousOn (fun z : ℂ ↦ f z / (z * (1 - conj a * z))) (Metric.sphere (0 : ℂ) 1) := by
    -- The only possible poles stay off the boundary circle in the inside-disc regime.
    refine hcont_f.div hcont_den ?_
    intro z hz
    exact mul_ne_zero
      (Metric.ne_of_mem_sphere hz one_ne_zero)
      (one_sub_conj_mul_ne_zero_on_closed_unitDisc (a := a) (z := z) ha
        (Metric.sphere_subset_closedBall hz))
  have hreflect :
      ((2 * Real.pi * I : ℂ)⁻¹) •
          (∮ z in C(0, (1 : ℝ)), conj (f z) / (z - a)) =
        conj (((2 * Real.pi * I : ℂ)⁻¹) •
          (∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z)))) :=
    unit_circle_conj_reflected_aux_normalized (f := f) (a := a) hg
  have hw0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self zero_lt_one
  have haux_value :
      ((2 * Real.pi * I : ℂ)⁻¹) •
          (∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z))) =
        f 0 := by
    have hkernel :
        ∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z)) =
          ∮ z in C(0, (1 : ℝ)), (z - 0)⁻¹ • hAux z := by
      -- Rewrite the auxiliary integrand into the standard Cauchy-kernel form.
      refine circleIntegral.integral_congr (show (0 : ℝ) ≤ 1 by norm_num) ?_
      intro z hz
      simp [hAux, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    calc
      ((2 * Real.pi * I : ℂ)⁻¹) •
          (∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z))) =
        ((2 * Real.pi * I : ℂ)⁻¹) •
          (∮ z in C(0, (1 : ℝ)), (z - 0)⁻¹ • hAux z) := by
        rw [hkernel]
      _ = hAux 0 := by
        simpa [hAux] using hAux_diff.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw0
      _ = f 0 := by
        simp [hAux]
  -- Evaluate the reflected auxiliary integral by Cauchy's formula and conjugate the result back.
  calc
    ((2 * Real.pi * I : ℂ)⁻¹) •
        (∮ z in C(0, (1 : ℝ)), conj (f z) / (z - a)) =
      conj (((2 * Real.pi * I : ℂ)⁻¹) •
        (∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z)))) := hreflect
    _ = conj (f 0) := by rw [haux_value]

/-- Exercise 3 (2): if `f` is holomorphic on a neighborhood of the closed unit disc, then the
same unit-circle Cauchy integral equals `conj (f 0) - conj (f (1 / conj a))` for `1 < ‖a‖`. -/
theorem
    unit_circle_conj_cauchy_integral_eq_conj_zero_sub_conj_inv_conj_of_one_lt_norm
    {a : ℂ}
    (ha : 1 < ‖a‖) :
    ((2 * Real.pi * I : ℂ)⁻¹) •
        (∮ z in C(0, (1 : ℝ)), conj (f z) / (z - a)) =
      conj (f 0) - conj (f (1 / conj a)) := by
  have hd : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) 1) :=
    analyticOnNhd_diffContOnCl_unitDisc (f := f) hf
  have ha0 : a ≠ 0 := by
    intro ha0
    have : ¬ ((1 : ℝ) < 0) := by norm_num
    exact this (by simpa [ha0] using ha)
  let w : ℂ := 1 / conj a
  have hw : w ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [w] using inv_conj_mem_unit_ball_of_one_lt_norm (a := a) ha
  have hw_norm : ‖w‖ < 1 := by
    simpa [w, Metric.mem_ball, dist_eq_norm] using hw
  have hz_ne_w : ∀ z ∈ Metric.sphere (0 : ℂ) 1, z ≠ w := by
    intro z hz hzw
    have : ‖w‖ = 1 := by simpa [hzw] using (mem_sphere_iff_norm.1 hz)
    exact (ne_of_lt hw_norm) this
  have hden_ne : ∀ z ∈ Metric.sphere (0 : ℂ) 1, 1 - conj a * z ≠ 0 := by
    intro z hz hzero
    have hcona : conj a ≠ 0 := by
      intro hcona
      apply ha0
      simpa using congrArg conj hcona
    have hmul : conj a * z = 1 := (sub_eq_zero.mp hzero).symm
    have hinv : z = 1 / conj a := by
      have hinv_mul := congrArg (fun t : ℂ => (conj a)⁻¹ * t) hmul
      simpa [hcona, mul_assoc, one_div] using hinv_mul
    exact hz_ne_w z hz (by simpa [w] using hinv)
  have hcont_f : ContinuousOn f (Metric.sphere (0 : ℂ) 1) :=
    (hd.continuousOn_ball).mono Metric.sphere_subset_closedBall
  have hcont_den :
      ContinuousOn (fun z : ℂ ↦ z * (1 - conj a * z)) (Metric.sphere (0 : ℂ) 1) := by
    -- The reflected denominator is polynomial, hence continuous on the boundary circle.
    exact continuousOn_id.mul (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
  have hg :
      ContinuousOn (fun z : ℂ ↦ f z / (z * (1 - conj a * z))) (Metric.sphere (0 : ℂ) 1) := by
    -- In the exterior case, both poles stay off the boundary because the reflected pole is inside.
    refine hcont_f.div hcont_den ?_
    intro z hz
    exact mul_ne_zero (Metric.ne_of_mem_sphere hz one_ne_zero) (hden_ne z hz)
  have hreflect :
      ((2 * Real.pi * I : ℂ)⁻¹) •
          (∮ z in C(0, (1 : ℝ)), conj (f z) / (z - a)) =
        conj (((2 * Real.pi * I : ℂ)⁻¹) •
          (∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z)))) :=
    unit_circle_conj_reflected_aux_normalized (f := f) (a := a) hg
  have hcont_kernel_zero :
      ContinuousOn (fun z : ℂ ↦ (z - 0)⁻¹) (Metric.sphere (0 : ℂ) 1) := by
    -- The kernel at `0` is continuous on the boundary circle because `0` is the center.
    refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
    intro z hz
    exact sub_ne_zero.2 (Metric.ne_of_mem_sphere hz one_ne_zero)
  have hcont_kernel_w :
      ContinuousOn (fun z : ℂ ↦ (z - w)⁻¹) (Metric.sphere (0 : ℂ) 1) := by
    -- The kernel at the reflected pole is also continuous because that pole lies strictly inside.
    refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
    intro z hz
    exact sub_ne_zero.2 (hz_ne_w z hz)
  have hterm_zero :
      CircleIntegrable (fun z : ℂ ↦ (z - 0)⁻¹ • f z) 0 1 := by
    refine ContinuousOn.circleIntegrable (show (0 : ℝ) ≤ 1 by norm_num) ?_
    exact hcont_kernel_zero.smul hcont_f
  have hterm_w :
      CircleIntegrable (fun z : ℂ ↦ (z - w)⁻¹ • f z) 0 1 := by
    refine ContinuousOn.circleIntegrable (show (0 : ℝ) ≤ 1 by norm_num) ?_
    exact hcont_kernel_w.smul hcont_f
  let I0 : ℂ := ∮ z in C(0, (1 : ℝ)), (z - 0)⁻¹ • f z
  let Iw : ℂ := ∮ z in C(0, (1 : ℝ)), (z - w)⁻¹ • f z
  have hsplit :
      ∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z)) = I0 - Iw := by
    have hrewrite :
        ∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z)) =
          ∮ z in C(0, (1 : ℝ)), (z - 0)⁻¹ • f z - (z - w)⁻¹ • f z := by
      -- Split the reflected kernel into the two ordinary Cauchy kernels at `0` and `w`.
      refine circleIntegral.integral_congr (show (0 : ℝ) ≤ 1 by norm_num) ?_
      intro z hz
      calc
        f z / (z * (1 - conj a * z)) = f z * (1 / (z * (1 - conj a * z))) := by
          simp [div_eq_mul_inv]
        _ = f z * (1 / z - 1 / (z - 1 / conj a)) := by
          rw [reciprocal_split_unit_circle_kernel_of_one_lt_norm (a := a) (z := z) ha0
            (Metric.ne_of_mem_sphere hz one_ne_zero) (by simpa [w] using hz_ne_w z hz)]
        _ = (z - 0)⁻¹ • f z - (z - w)⁻¹ • f z := by
          simp [w, smul_eq_mul, div_eq_mul_inv, sub_eq_add_neg]
          ring_nf
    calc
      ∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z)) =
        ∮ z in C(0, (1 : ℝ)), (z - 0)⁻¹ • f z - (z - w)⁻¹ • f z := hrewrite
      _ = I0 - Iw := by
        simpa [I0, Iw] using circleIntegral.integral_sub hterm_zero hterm_w
  have hw0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self zero_lt_one
  have hI0 :
      ((2 * Real.pi * I : ℂ)⁻¹) • I0 = f 0 := by
    simpa [I0] using hd.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw0
  have hIw :
      ((2 * Real.pi * I : ℂ)⁻¹) • Iw = f w := by
    simpa [Iw] using hd.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  have haux_value :
      ((2 * Real.pi * I : ℂ)⁻¹) •
          (∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z))) =
        f 0 - f w := by
    -- Each split term is a standard Cauchy integral inside the unit disc.
    calc
      ((2 * Real.pi * I : ℂ)⁻¹) •
          (∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z))) =
        ((2 * Real.pi * I : ℂ)⁻¹) • (I0 - Iw) := by
        rw [hsplit]
      _ = ((2 * Real.pi * I : ℂ)⁻¹) • I0 - ((2 * Real.pi * I : ℂ)⁻¹) • Iw := by
        simpa using smul_sub ((2 * Real.pi * I : ℂ)⁻¹) I0 Iw
      _ = f 0 - f w := by rw [hI0, hIw]
  -- Route correction: the exterior case still follows the reflected-circle route; the only extra
  -- step is the boundary partial-fraction split at the reflected interior pole `w = 1 / conj a`.
  calc
    ((2 * Real.pi * I : ℂ)⁻¹) •
        (∮ z in C(0, (1 : ℝ)), conj (f z) / (z - a)) =
      conj (((2 * Real.pi * I : ℂ)⁻¹) •
        (∮ z in C(0, (1 : ℝ)), f z / (z * (1 - conj a * z)))) := hreflect
    _ = conj (f 0 - f w) := by rw [haux_value]
    _ = conj (f 0) - conj (f (1 / conj a)) := by
      simp [w, map_sub]

end
