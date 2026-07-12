import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling note: this item lives in one-variable complex analysis for planar curves written
-- in complex notation. The relevant core/canonical owners are:
-- * `AnalyticAt` / `AnalyticAt.contDiffAt` for the local holomorphic-to-`C²` regularity layer;
-- * `iteratedDeriv` for higher real derivatives of the parametrized curve;
-- * `deriv_circleMap` / `analyticOnNhd_circleMap` for the canonical circle parametrization.
-- There is no upstream curvature owner in the project or mathlib. The source-facing notion for
-- this exercise is therefore a minimal local owner `reciprocalRadiusOfCurvature`, whose defining
-- formula stays on the canonical derivative API. The regularity input belongs at theorem level,
-- via the canonical owner `ContDiffAt`, when deriving that formula from holomorphy rather than as
-- primitive data of the curvature owner itself.

/-- The reciprocal radius of curvature of a regular complex plane curve at parameter `t`,
written in terms of its first and second real derivatives. -/
noncomputable def reciprocalRadiusOfCurvature
    (γ : ℝ → ℂ) (t : ℝ) (hγ : deriv γ t ≠ 0) : ℝ :=
  Complex.im (iteratedDeriv 2 γ t * ↑((Units.mk0 (deriv γ t) hγ)⁻¹)) *
    ↑((Units.mk0 ‖deriv γ t‖ (by simpa using norm_ne_zero_iff.mpr hγ))⁻¹)

/-- Bridge from the source-facing reciprocal-radius owner to the textbook derivative formula. -/
theorem reciprocalRadiusOfCurvature_eq
    (γ : ℝ → ℂ) (t : ℝ) (hγ : deriv γ t ≠ 0) :
    reciprocalRadiusOfCurvature γ t hγ =
      Complex.im (iteratedDeriv 2 γ t / deriv γ t) / ‖deriv γ t‖ := by
  simp [reciprocalRadiusOfCurvature, div_eq_mul_inv]

/-- A holomorphic germ sends the unit-circle parametrization to a `C²` complex plane curve. -/
theorem holomorphic_image_circle_contDiffAt
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    ContDiffAt ℝ 2 (fun θ ↦ f (a * circleMap 0 1 θ)) 0 := by
  have hcircle : AnalyticAt ℝ (fun θ ↦ a * circleMap 0 1 θ) 0 := by
    exact analyticAt_const.mul ((analyticOnNhd_circleMap 0 1) 0 (by simp))
  exact (hf.restrictScalars.comp_of_eq hcircle (by simp [circleMap_zero])).contDiffAt

/-- Helper for Exercise 4: the unit-circle parametrization scaled by `a` has initial velocity
`a * I`. -/
lemma scaled_circleMap_deriv_zero {a : ℂ} :
    deriv (fun θ ↦ a * circleMap 0 1 θ) 0 = a * Complex.I := by
  -- Differentiate the scaled unit-circle parametrization directly at the base point.
  have h :
      HasDerivAt (fun θ : ℝ ↦ a * circleMap 0 1 θ) (a * (circleMap 0 1 0 * Complex.I)) 0 := by
    simpa using (hasDerivAt_circleMap 0 1 0).const_mul a
  simpa [circleMap_zero, mul_assoc] using h.deriv

/-- Helper for Exercise 4: the scaled unit-circle parametrization has initial acceleration `-a`. -/
lemma scaled_circleMap_iteratedDeriv_two_zero {a : ℂ} :
    iteratedDeriv 2 (fun θ ↦ a * circleMap 0 1 θ) 0 = -a := by
  -- First compute the second derivative of the unit circle itself.
  have hcircle :
      iteratedDeriv 2 (circleMap 0 1) 0 = -1 := by
    have hderiv : deriv (circleMap 0 1) = fun θ ↦ circleMap 0 1 θ * Complex.I := by
      exact deriv_eq fun θ ↦ hasDerivAt_circleMap 0 1 θ
    have hsecond :
        deriv (fun θ : ℝ ↦ circleMap 0 1 θ * Complex.I) =
          fun θ ↦ (circleMap 0 1 θ * Complex.I) * Complex.I := by
      exact deriv_eq fun θ ↦ (hasDerivAt_circleMap 0 1 θ).mul_const Complex.I
    have hderiv2 :
        deriv (deriv (circleMap 0 1)) 0 = (circleMap 0 1 0 * Complex.I) * Complex.I := by
      rw [hderiv, hsecond]
    calc
      iteratedDeriv 2 (circleMap 0 1) 0 = deriv (deriv (circleMap 0 1)) 0 := by
            simp [iteratedDeriv_succ]
      _ = (circleMap 0 1 0 * Complex.I) * Complex.I := hderiv2
      _ = -1 := by
            simp [circleMap_zero]
  calc
    iteratedDeriv 2 (fun θ ↦ a * circleMap 0 1 θ) 0 = a * iteratedDeriv 2 (circleMap 0 1) 0 := by
          simpa using (iteratedDeriv_const_mul_field (n := 2) (x := 0) a (circleMap 0 1))
    _ = a * (-1) := by rw [hcircle]
    _ = -a := by ring

/-- Helper for Exercise 4: the image curve has initial velocity `a * I * f'(a)`. -/
lemma holomorphic_image_circle_deriv_zero
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    deriv (fun θ ↦ f (a * circleMap 0 1 θ)) 0 = a * Complex.I * deriv f a := by
  -- Differentiate the composition `f ∘ (θ ↦ a * circleMap 0 1 θ)` by the chain rule.
  have hinner : HasDerivAt (fun θ : ℝ ↦ a * circleMap 0 1 θ) (a * Complex.I) 0 := by
    simpa [circleMap_zero, mul_assoc] using (hasDerivAt_circleMap 0 1 0).const_mul a
  have hcomp :
      HasDerivAt (fun θ : ℝ ↦ f (a * circleMap 0 1 θ)) ((a * Complex.I) * deriv f a) 0 := by
    simpa [circleMap_zero, mul_assoc] using
      (HasDerivAt.scomp_of_eq (hg := hf.differentiableAt.hasDerivAt)
        (hh := hinner) (hy := by simp [circleMap_zero]))
  simpa [mul_assoc] using hcomp.deriv

/-- Helper for Exercise 4: the real second Fréchet derivative of a holomorphic function evaluated
twice on `a * I` matches the complex second derivative. -/
lemma holomorphic_iteratedFDeriv_two_apply_scaled_I
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    iteratedFDeriv ℝ 2 f a (fun _ ↦ a * Complex.I) = -a ^ 2 * iteratedDeriv 2 f a := by
  -- Restrict scalars from `ℂ` to `ℝ` and then evaluate on the constant vector `a * I`.
  have hrestrict :
      ContinuousMultilinearMap.restrictScalars ℝ (iteratedFDeriv ℂ 2 f a) =
        iteratedFDeriv ℝ 2 f a := by
    simpa using
      ((hf.contDiffAt : ContDiffAt ℂ 2 f a).restrictScalars_iteratedFDeriv (𝕜 := ℝ))
  calc
    iteratedFDeriv ℝ 2 f a (fun _ ↦ a * Complex.I) =
        (ContinuousMultilinearMap.restrictScalars ℝ (iteratedFDeriv ℂ 2 f a))
          (fun _ ↦ a * Complex.I) := by
          rw [← hrestrict]
    _ = iteratedFDeriv ℂ 2 f a (fun _ ↦ a * Complex.I) := by
          simp [ContinuousMultilinearMap.coe_restrictScalars]
    _ = (a * Complex.I) ^ 2 * iteratedDeriv 2 f a := by
          simp [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, pow_two, smul_eq_mul]
    _ = -a ^ 2 * iteratedDeriv 2 f a := by
          simp [pow_two, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 4: the image of the scaled unit circle has the expected initial
acceleration. -/
lemma holomorphic_image_circle_iteratedDeriv_two_zero
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    iteratedDeriv 2 (fun θ ↦ f (a * circleMap 0 1 θ)) 0 =
      -a * deriv f a - a ^ 2 * iteratedDeriv 2 f a := by
  -- Differentiate the composition twice using the canonical second-order chain rule.
  have houter :
      ContDiffAt ℝ 2 f ((fun θ : ℝ ↦ a * circleMap 0 1 θ) 0) := by
    simpa [circleMap_zero] using hf.restrictScalars.contDiffAt
  have hinner :
      ContDiffAt ℝ 2 (fun θ ↦ a * circleMap 0 1 θ) 0 := by
    have hanalytic : AnalyticAt ℝ (fun θ ↦ a * circleMap 0 1 θ) 0 := by
      exact analyticAt_const.mul ((analyticOnNhd_circleMap 0 1) 0 (by simp))
    exact hanalytic.contDiffAt
  have hfderiv_apply :
      fderiv ℝ f a (-a) = -a * deriv f a := by
    -- Evaluate the real Fréchet derivative of `f` on the acceleration vector `-a`.
    have hfd :=
      congrArg (fun L : ℂ →L[ℝ] ℂ => L (-a))
        hf.differentiableAt.hasDerivAt.complexToReal_fderiv.fderiv
    simpa [ContinuousLinearMap.smul_apply, mul_assoc, mul_left_comm, mul_comm] using hfd
  have hcomp :=
    iteratedDeriv_vcomp_two
      (g := f) (f := fun θ : ℝ ↦ a * circleMap 0 1 θ) (x := 0) houter hinner
  -- Replace each term in the chain-rule identity by the explicit circle computations.
  have hz : (fun θ : ℝ ↦ a * circleMap 0 1 θ) 0 = a := by
    simp [circleMap_zero]
  rw [hz, scaled_circleMap_deriv_zero, scaled_circleMap_iteratedDeriv_two_zero] at hcomp
  rw [holomorphic_iteratedFDeriv_two_apply_scaled_I (hf := hf), hfderiv_apply] at hcomp
  simpa [Function.comp, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hcomp

/-- Exercise 4. Let `Γ` be represented near `f a` by the canonical parametrized curve
`θ ↦ f (a * exp (i θ))`, i.e. `θ ↦ f (a * circleMap 0 1 θ)`. If `f` is holomorphic at `a` and
this parametrized curve is regular at `θ = 0`, then the
reciprocal radius of curvature of `Γ` at `f a` is
`(Complex.re (a * f''(a) / f'(a)) + 1) / ‖a * f'(a)‖`. -/
theorem holomorphic_image_circle_reciprocal_radius_formula
    {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a)
    (hγ : deriv (fun θ ↦ f (a * circleMap 0 1 θ)) 0 ≠ 0) :
    reciprocalRadiusOfCurvature (fun θ ↦ f (a * circleMap 0 1 θ)) 0 hγ =
      (Complex.re (a * iteratedDeriv 2 f a / deriv f a) + 1) / ‖a * deriv f a‖ := by
  -- Rewrite curvature using the textbook quotient of second and first derivatives.
  rw [reciprocalRadiusOfCurvature_eq]
  set A : ℂ := a * iteratedDeriv 2 f a / deriv f a with hA
  set u : ℂ := a * deriv f a with hu_def
  have hderiv := holomorphic_image_circle_deriv_zero hf
  have hiter := holomorphic_image_circle_iteratedDeriv_two_zero hf
  have hprod_nonzero : a * deriv f a ≠ 0 := by
    -- Regularity of the image curve forces the velocity factor `a * f'(a)` to be nonzero.
    intro hzero
    apply hγ
    rw [hderiv]
    calc
      a * Complex.I * deriv f a = (a * deriv f a) * Complex.I := by
        simp [mul_left_comm, mul_comm]
      _ = 0 := by simp [hzero]
  have hu_nonzero : u ≠ 0 := by
    simpa [hu_def] using hprod_nonzero
  have hderiv_ne : deriv f a ≠ 0 := by
    exact (mul_ne_zero_iff.mp hprod_nonzero).2
  have hcancel :
      (a * deriv f a) * (a * iteratedDeriv 2 f a / deriv f a) = a ^ 2 * iteratedDeriv 2 f a := by
    -- Cancel the single factor `f'(a)` that appears in the denominator.
    calc
      (a * deriv f a) * (a * iteratedDeriv 2 f a / deriv f a) =
          (a * a * iteratedDeriv 2 f a) * (deriv f a * (deriv f a)⁻¹) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = a ^ 2 * iteratedDeriv 2 f a := by
            simp [pow_two, hderiv_ne]
  have hfactor :
      -a * deriv f a - a ^ 2 * iteratedDeriv 2 f a = -u * (1 + A) := by
    -- Factor the second derivative so the quotient collapses to a pure `I` factor.
    calc
      -a * deriv f a - a ^ 2 * iteratedDeriv 2 f a = -(a * deriv f a) - a ^ 2 * iteratedDeriv 2 f a := by
            ring
      _ =
          -(a * deriv f a) - (a * deriv f a) * (a * iteratedDeriv 2 f a / deriv f a) := by
            rw [hcancel]
      _ = -(a * deriv f a) + -((a * deriv f a) * (a * iteratedDeriv 2 f a / deriv f a)) := by
            simp [sub_eq_add_neg]
      _ = -u * (1 + A) := by
            simp [hu_def, hA, mul_add, mul_assoc]
  have hunit : (-u) / (u * Complex.I) = Complex.I := by
    -- The residual unit quotient is exactly `I`.
    field_simp [hu_nonzero]
    simp [Complex.I_sq]
  have hquot :
      iteratedDeriv 2 (fun θ ↦ f (a * circleMap 0 1 θ)) 0 /
          deriv (fun θ ↦ f (a * circleMap 0 1 θ)) 0 =
        (1 + A) * Complex.I := by
    -- Combine the derivative formulas and normalize the complex quotient.
    rw [hiter, hderiv, hfactor]
    calc
      (-u * (1 + A)) / (a * Complex.I * deriv f a) = (-u * (1 + A)) / (u * Complex.I) := by
        simp [hu_def, mul_assoc, mul_left_comm, mul_comm]
      _ = (1 + A) * ((-u) / (u * Complex.I)) := by
        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = (1 + A) * Complex.I := by rw [hunit]
  have hnorm :
      ‖deriv (fun θ ↦ f (a * circleMap 0 1 θ)) 0‖ = ‖u‖ := by
    -- The factor `I` has norm `1`, so it does not change the speed.
    rw [hderiv, hu_def]
    simpa [mul_assoc, mul_left_comm, mul_comm] using (norm_mul (a * deriv f a) Complex.I)
  -- Read off the imaginary part after multiplication by `I`.
  calc
    Complex.im
        (iteratedDeriv 2 (fun θ ↦ f (a * circleMap 0 1 θ)) 0 /
          deriv (fun θ ↦ f (a * circleMap 0 1 θ)) 0) /
        ‖deriv (fun θ ↦ f (a * circleMap 0 1 θ)) 0‖ =
      Complex.im ((1 + A) * Complex.I) / ‖u‖ := by rw [hquot, hnorm]
    _ = Complex.re (1 + A) / ‖u‖ := by rw [Complex.mul_I_im]
    _ = (A.re + 1) / ‖u‖ := by simp [add_comm]
    _ = (Complex.re (a * iteratedDeriv 2 f a / deriv f a) + 1) / ‖a * deriv f a‖ := by
      simp [hA, hu_def]
