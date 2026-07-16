import DifferentialForms_Cartan_1970.cartan.III.section12.«0034_Exercise_21».NegativeAxisKeyholeRange

noncomputable section

open Complex MeasureTheory
open scoped Real unitInterval

/-- Helper for Exercise 21: a holomorphic kernel of the form `g(z) / (z - a)` realizes its
residue `g(a)` on every positively oriented small circle that stays inside both `interior K` and
`D`. -/
lemma localResidueCircle_div_sub_of_differentiableOn
    {K D : Set ℂ} {g : ℂ → ℂ} {a : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hK : Metric.closedBall a r ⊆ interior K)
    (hD : Metric.closedBall a r ⊆ D)
    (hg : DifferentiableOn ℂ g D) :
    LocalResidueCircle K D (fun z ↦ g z / (z - a)) a (g a) := by
  -- Choose the given circle and evaluate its Cauchy kernel integral by the disc Cauchy formula.
  refine ⟨r, hr, hK, hD, ?_⟩
  have hg_ball : DifferentiableOn ℂ g (Metric.closedBall a r) := hg.mono hD
  have ha_ball : a ∈ Metric.ball a r := by
    exact (Metric.mem_ball_self hr : a ∈ Metric.ball a r)
  simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    hg_ball.circleIntegral_sub_inv_smul ha_ball

/-- Helper for Exercise 21: the principal logarithm factors as `(z - 1)` times the first divided
difference `dslope log 1 z`. -/
lemma exercise21_log_eq_sub_one_mul_dslope (z : ℂ) :
    Complex.log z = (z - 1) * dslope Complex.log 1 z := by
  -- This is the standard divided-difference identity specialized at the simple zero of `log`.
  simpa [Complex.log_one] using (sub_smul_dslope Complex.log 1 z).symm

/-- Helper for Exercise 21: the factor `log z` can be rewritten through `dslope log 1 z`, so the
integrand takes the standard `/(z - 1)` kernel form. -/
lemma exercise21_integrand_eq_real_pole_kernel (a : ℝ) {z : ℂ} :
    (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) =
      (((z ^ 2 + (a : ℂ) ^ 2) * dslope Complex.log 1 z)⁻¹) / (z - 1) := by
  -- Rewrite `log z` by its divided-difference factor and normalize the resulting reciprocal.
  rw [exercise21_log_eq_sub_one_mul_dslope]
  field_simp

/-- Helper for Exercise 21: away from `z = a i`, the integrand is a standard simple-pole kernel
with coefficient `(((z + a i) * log z)⁻¹)`. -/
lemma exercise21_integrand_eq_pos_imag_pole_kernel (a : ℝ) {z : ℂ}
    (hz : z ≠ (a : ℂ) * Complex.I) :
    (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) =
      ((((z + (a : ℂ) * Complex.I) * Complex.log z)⁻¹) / (z - (a : ℂ) * Complex.I)) := by
  -- Factor `z² + a²` as `(z - ai)(z + ai)` and isolate the simple pole at `z = ai`.
  have hz' : z - (a : ℂ) * Complex.I ≠ 0 := sub_ne_zero.mpr hz
  calc
    (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹)
        = ((((z - (a : ℂ) * Complex.I) * (z + (a : ℂ) * Complex.I)) * Complex.log z)⁻¹) := by
            congr 1
            ring_nf
            simp [pow_two]
    _ = ((((z + (a : ℂ) * Complex.I) * Complex.log z)⁻¹) / (z - (a : ℂ) * Complex.I)) := by
          field_simp [hz']

/-- Helper for Exercise 21: away from `z = -a i`, the integrand is a standard simple-pole kernel
with coefficient `(((z - a i) * log z)⁻¹)`. -/
lemma exercise21_integrand_eq_neg_imag_pole_kernel (a : ℝ) {z : ℂ}
    (hz : z ≠ -((a : ℂ) * Complex.I)) :
    (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) =
      ((((z - (a : ℂ) * Complex.I) * Complex.log z)⁻¹) / (z + (a : ℂ) * Complex.I)) := by
  -- Factor `z² + a²` as `(z + ai)(z - ai)` and isolate the simple pole at `z = -ai`.
  have hz' : z + (a : ℂ) * Complex.I ≠ 0 := by
    simpa [eq_neg_iff_add_eq_zero] using hz
  calc
    (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹)
        = ((((z + (a : ℂ) * Complex.I) * (z - (a : ℂ) * Complex.I)) * Complex.log z)⁻¹) := by
            congr 1
            ring_nf
            simp [pow_two]
    _ = ((((z - (a : ℂ) * Complex.I) * Complex.log z)⁻¹) / (z + (a : ℂ) * Complex.I)) := by
          field_simp [hz']

/-- Helper for Exercise 21: on the principal branch, `log (a i)` is `log a + π i / 2` for
positive real `a`. -/
lemma exercise21_log_mul_I_of_pos (a : ℝ) (ha : 0 < a) :
    Complex.log ((a : ℂ) * Complex.I) = Real.log a + (Real.pi / 2 : ℝ) * Complex.I := by
  -- Factor out the positive real scalar so that the branch value reduces to `log I`.
  simpa [Complex.log_I, add_comm] using
    (Complex.log_ofReal_mul (x := Complex.I) ha Complex.I_ne_zero)

/-- Helper for Exercise 21: on the principal branch, `log (-a i)` is `log a - π i / 2` for
positive real `a`. -/
lemma exercise21_log_neg_mul_I_of_pos (a : ℝ) (ha : 0 < a) :
    Complex.log (-((a : ℂ) * Complex.I)) = Real.log a - (Real.pi / 2 : ℝ) * Complex.I := by
  -- Rewrite `-a i` as the positive real `a` times `-I`, then use the principal-branch value of
  -- `log (-I)`.
  rw [show -((a : ℂ) * Complex.I) = (a : ℂ) * (-Complex.I) by ring]
  simpa [Complex.log_neg_I, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (Complex.log_ofReal_mul (x := -Complex.I) ha (by simp : (-Complex.I) ≠ 0))

/-- Helper for Exercise 21: the pole at `z = 1` already contributes a real-valued term. -/
lemma exercise21_real_pole_term (a : ℝ) :
    1 / ((1 : ℂ) + (a : ℂ) ^ 2) = (1 / (1 + a ^ 2) : ℂ) := by
  -- The denominator is a real scalar, so the complex reciprocal is just the coerced real one.
  simp [pow_two]

/-- Helper for Exercise 21: expand the denominator at `z = a i` into explicit real and imaginary
parts. -/
lemma exercise21_term2_rewrite (a : ℝ) :
    ((2 * (a : ℂ) * Complex.I) * (Real.log a + (Real.pi / 2 : ℝ) * Complex.I)) =
      (-(a * Real.pi) : ℝ) + ((2 * a * Real.log a : ℝ) : ℂ) * Complex.I := by
  -- This is the direct multiplication needed before taking reciprocals.
  rw [Complex.ext_iff]
  constructor
  · simp [mul_add, mul_assoc]
    ring
  · simp [mul_add, mul_assoc]

/-- Helper for Exercise 21: expand the denominator at `z = -a i` into explicit real and imaginary
parts. -/
lemma exercise21_term3_rewrite (a : ℝ) :
    ((2 * (a : ℂ) * Complex.I) * (Real.log a - (Real.pi / 2 : ℝ) * Complex.I)) =
      ((a * Real.pi : ℝ) : ℂ) + ((2 * a * Real.log a : ℝ) : ℂ) * Complex.I := by
  -- The same expansion with the opposite branch value flips the real part.
  rw [Complex.ext_iff]
  constructor
  · simp [sub_eq_add_neg, mul_add, mul_assoc]
    ring
  · simp [sub_eq_add_neg, mul_add, mul_assoc]

/-- Helper for Exercise 21: after substituting the principal-branch values of
`log (± a i)`, the two nonreal residue terms combine to a single real correction. -/
lemma exercise21_reciprocal_difference (a : ℝ) (ha : 0 < a) :
    1 / (((-(a * Real.pi) : ℝ) : ℂ) + ((2 * a * Real.log a : ℝ) : ℂ) * Complex.I) -
      1 / (((a * Real.pi : ℝ) : ℂ) + ((2 * a * Real.log a : ℝ) : ℂ) * Complex.I) =
        (-Real.pi / (2 * a * ((Real.log a) ^ 2 + Real.pi ^ 2 / 4)) : ℝ) := by
  -- Separate real and imaginary parts of the reciprocal difference; the imaginary part cancels.
  rw [Complex.ext_iff]
  constructor
  · simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.normSq, pow_two]
    field_simp [ha.ne', Real.pi_ne_zero]
    ring
  · simp [Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_im, Complex.normSq, pow_two]

/-- Helper for Exercise 21: the explicit residue sum in the contour identity simplifies to the
real quantity that appears in the final integral formula. -/
lemma exercise21_residue_sum_eval (a : ℝ) (ha : 0 < a) :
    1 / ((1 : ℂ) + (a : ℂ) ^ 2) +
      1 / ((2 * (a : ℂ) * Complex.I) * Complex.log ((a : ℂ) * Complex.I)) -
      1 / ((2 * (a : ℂ) * Complex.I) * Complex.log (-((a : ℂ) * Complex.I))) =
        (1 / (1 + a ^ 2) - Real.pi / (2 * a * ((Real.log a) ^ 2 + Real.pi ^ 2 / 4)) : ℝ) := by
  -- Substitute the principal-branch logarithms and rewrite the two reciprocal denominators.
  rw [exercise21_log_mul_I_of_pos a ha, exercise21_log_neg_mul_I_of_pos a ha]
  rw [exercise21_term2_rewrite, exercise21_term3_rewrite, exercise21_real_pole_term]
  have hrec := exercise21_reciprocal_difference a ha
  -- Regroup the sum so the reciprocal-difference helper applies directly.
  calc
    (1 / (1 + a ^ 2) : ℂ) +
        1 / (((-(a * Real.pi) : ℝ) : ℂ) + ((2 * a * Real.log a : ℝ) : ℂ) * Complex.I) -
        1 / (((a * Real.pi : ℝ) : ℂ) + ((2 * a * Real.log a : ℝ) : ℂ) * Complex.I) =
          (1 / (1 + a ^ 2) : ℂ) +
            (1 / (((-(a * Real.pi) : ℝ) : ℂ) + ((2 * a * Real.log a : ℝ) : ℂ) * Complex.I) -
              1 / (((a * Real.pi : ℝ) : ℂ) + ((2 * a * Real.log a : ℝ) : ℂ) * Complex.I)) := by
            simp [sub_eq_add_neg, add_assoc]
    _ = (1 / (1 + a ^ 2) : ℂ) +
          (-Real.pi / (2 * a * ((Real.log a) ^ 2 + Real.pi ^ 2 / 4)) : ℝ) := by
            exact congrArg (fun z : ℂ => (1 / (1 + a ^ 2) : ℂ) + z) hrec
    _ = (1 / (1 + a ^ 2) - Real.pi / (2 * a * ((Real.log a) ^ 2 + Real.pi ^ 2 / 4)) : ℝ) := by
          simp [sub_eq_add_neg]
          ring_nf

/-- Helper for Exercise 21: the three poles of the slit-plane contour integrand are `1` and
`± a i`. -/
abbrev exercise21PoleSet (a : ℝ) : Set ℂ :=
  ({(1 : ℂ), (a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)} : Set ℂ)

/-- Helper for Exercise 21: the same finite pole set, packaged as a `Finset` for the residue
theorem. -/
abbrev exercise21PoleFinset (a : ℝ) : Finset ℂ :=
  {(1 : ℂ), (a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)}

/-- Helper for Exercise 21: coercing the pole `Finset` back to a set recovers the textbook pole
set. -/
lemma exercise21PoleFinset_coe (a : ℝ) :
    (↑(exercise21PoleFinset a) : Set ℂ) = exercise21PoleSet a := by
  ext z
  simp [exercise21PoleFinset, exercise21PoleSet]

/-- Helper for Exercise 21: the residue coefficient of the real pole at `z = 1`. -/
abbrev exercise21RealPoleCoeff (a : ℝ) : ℂ :=
  1 / ((1 : ℂ) + (a : ℂ) ^ 2)

/-- Helper for Exercise 21: the residue coefficient of the pole at `z = a i`. -/
abbrev exercise21PosImagPoleCoeff (a : ℝ) : ℂ :=
  1 / ((2 * (a : ℂ) * Complex.I) * Complex.log ((a : ℂ) * Complex.I))

/-- Helper for Exercise 21: the residue coefficient of the pole at `z = -a i`. -/
abbrev exercise21NegImagPoleCoeff (a : ℝ) : ℂ :=
  -1 / ((2 * (a : ℂ) * Complex.I) * Complex.log (-((a : ℂ) * Complex.I)))

/-- Helper for Exercise 21: the residue function on the three poles `1`, `a i`, and `-a i`. -/
abbrev exercise21Residue (a : ℝ) (z : ℂ) : ℂ :=
  if z = (1 : ℂ) then exercise21RealPoleCoeff a
  else if z = (a : ℂ) * Complex.I then exercise21PosImagPoleCoeff a
  else exercise21NegImagPoleCoeff a

/-- Helper for Exercise 21: the raw integrand after subtracting the three principal-part kernels.
This keeps the source contour decomposition explicit while separating the remaining
removable-singularity work from the already solved residue algebra. -/
abbrev exercise21RegularPart (a : ℝ) (z : ℂ) : ℂ :=
  (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) -
    exercise21RealPoleCoeff a / (z - 1) -
      exercise21PosImagPoleCoeff a / (z - (a : ℂ) * Complex.I) -
        exercise21NegImagPoleCoeff a / (z + (a : ℂ) * Complex.I)

/-- Helper for Exercise 21: on `Complex.slitPlane`, the principal logarithm vanishes only at `1`.
This is the bridge from the slit-plane branch choice to the nonvanishing denominator needed for
the punctured holomorphy statements below. -/
lemma exercise21_log_ne_zero_of_mem_slitPlane_ne_one {z : ℂ}
    (hz_slit : z ∈ Complex.slitPlane) (hz1 : z ≠ (1 : ℂ)) :
    Complex.log z ≠ 0 := by
  -- Exponentiating `log z = 0` on the slit plane would force `z = 1`.
  intro hz_log
  have hz_exp : Complex.exp (Complex.log z) = z :=
    Complex.exp_log (Complex.slitPlane_ne_zero hz_slit)
  rw [hz_log, Complex.exp_zero] at hz_exp
  exact hz1 hz_exp.symm

/-- Helper for Exercise 21: once the two imaginary poles are excluded, the quadratic factor
`z^2 + a^2` is nonzero. -/
lemma exercise21_quadratic_ne_zero_of_off_imag_poles (a : ℝ) {z : ℂ}
    (hz_ai : z ≠ (a : ℂ) * Complex.I) (hz_neg_ai : z ≠ -((a : ℂ) * Complex.I)) :
    z ^ 2 + (a : ℂ) ^ 2 ≠ 0 := by
  -- Factor the quadratic as `(z - a i) (z + a i)` and use the excluded-pole hypotheses.
  intro hquad
  have hfactor : z ^ 2 + (a : ℂ) ^ 2 =
      (z - (a : ℂ) * Complex.I) * (z + (a : ℂ) * Complex.I) := by
    ring_nf
    simp [pow_two]
  rw [hfactor] at hquad
  rcases mul_eq_zero.mp hquad with hleft | hright
  · exact hz_ai (sub_eq_zero.mp hleft)
  · exact hz_neg_ai (eq_neg_iff_add_eq_zero.mpr hright)

/-- Helper for Exercise 21: `Complex.log` is holomorphic on the principal slit plane. -/
lemma exercise21_log_differentiableOn_slitPlane :
    DifferentiableOn ℂ Complex.log Complex.slitPlane := by
  -- This is the standard holomorphy statement for the principal branch.
  intro z hz
  simpa using (Complex.hasDerivAt_log hz).differentiableAt.differentiableWithinAt

/-- Helper for Exercise 21: the divided difference `dslope log 1` never vanishes on
`Complex.slitPlane`. -/
lemma exercise21_dslope_log_ne_zero_of_mem_slitPlane {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    dslope Complex.log 1 z ≠ 0 := by
  -- Away from `1`, vanishing of the divided difference would force `log z = 0`; at `1`, the
  -- value is the derivative `log'(1) = 1`.
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1
    have hderiv : deriv Complex.log (1 : ℂ) = 1 := by
      simpa using
        (Complex.hasDerivAt_log
          (by simp [Complex.mem_slitPlane_iff] : (1 : ℂ) ∈ Complex.slitPlane)).deriv
    simpa [dslope_same, hderiv]
  · intro hdslope
    have hlog_ne : Complex.log z ≠ 0 :=
      exercise21_log_ne_zero_of_mem_slitPlane_ne_one hz hz1
    have hlog_zero : Complex.log z = 0 := by
      rw [exercise21_log_eq_sub_one_mul_dslope, hdslope]
      simp
    exact hlog_ne hlog_zero

/-- Helper for Exercise 21: the contour integrand is holomorphic at every slit-plane point away
from the three poles `1`, `± a i`. -/
lemma exercise21_integrand_differentiableAt_of_mem_slitPlane_off_poles
    (a : ℝ) {z : ℂ} (hz_slit : z ∈ Complex.slitPlane) (hz_off : z ∉ exercise21PoleSet a) :
    DifferentiableAt ℂ (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹)) z := by
  -- Excluding the three poles makes each denominator factor nonzero, so the inverse is holomorphic.
  have hz1 : z ≠ (1 : ℂ) := by
    intro hz1
    exact hz_off (by simp [exercise21PoleSet, hz1])
  have hz_ai : z ≠ (a : ℂ) * Complex.I := by
    intro hz_ai
    exact hz_off (by simp [exercise21PoleSet, hz_ai])
  have hz_neg_ai : z ≠ -((a : ℂ) * Complex.I) := by
    intro hz_neg_ai
    exact hz_off (by simp [exercise21PoleSet, hz_neg_ai])
  have hlog_ne : Complex.log z ≠ 0 :=
    exercise21_log_ne_zero_of_mem_slitPlane_ne_one hz_slit hz1
  have hquad_ne : z ^ 2 + (a : ℂ) ^ 2 ≠ 0 :=
    exercise21_quadratic_ne_zero_of_off_imag_poles a hz_ai hz_neg_ai
  have hdenom_ne : ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z) ≠ 0 :=
    mul_ne_zero hquad_ne hlog_ne
  have hquad : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ 2 + (a : ℂ) ^ 2) z := by
    fun_prop
  have hlog : DifferentiableAt ℂ Complex.log z := by
    simpa using (Complex.hasDerivAt_log hz_slit).differentiableAt
  -- The inverse of the nonvanishing denominator carries the final differentiability step.
  simpa using (hquad.mul hlog).inv hdenom_ne

/-- Helper for Exercise 21: the contour integrand is holomorphic on the slit plane once the three
actual poles are removed. -/
lemma exercise21_integrand_differentiableOn_slitPlane_off_poles
    (a : ℝ) :
    DifferentiableOn ℂ
      (fun z ↦ (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹))
      (Complex.slitPlane \ exercise21PoleSet a) := by
  -- Unpack the punctured-slit condition and reuse the pointwise differentiability bridge.
  intro z hz
  have hdiff :
      DifferentiableAt ℂ (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹)) z :=
    exercise21_integrand_differentiableAt_of_mem_slitPlane_off_poles a hz.1 hz.2
  exact hdiff.differentiableWithinAt

/-- Helper for Exercise 21: the punctured-slit holomorphy statement can be restated with the
`Finset` pole package used by the residue theorem. -/
lemma exercise21_integrand_differentiableOn_slitPlane_off_poles_finset
    (a : ℝ) :
    DifferentiableOn ℂ
      (fun z ↦ (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹))
      (Complex.slitPlane \ (↑(exercise21PoleFinset a) : Set ℂ)) := by
  -- This is just the set-level pole description rewritten through `exercise21PoleFinset`.
  simpa [exercise21PoleFinset_coe] using
    exercise21_integrand_differentiableOn_slitPlane_off_poles a

/-- Helper for Exercise 21: after subtracting the three residue kernels, the remaining raw term is
holomorphic on the punctured slit plane. Because Lean totalizes `inv 0 = 0`, extending this raw
expression across the poles is the separate remaining blocker rather than part of this lemma. -/
lemma exercise21_regularPart_differentiableOn_slitPlane_off_poles
    (a : ℝ) :
    DifferentiableOn ℂ (exercise21RegularPart a) (Complex.slitPlane \ exercise21PoleSet a) := by
  intro z hz
  have hz_slit : z ∈ Complex.slitPlane := hz.1
  have hz_off : z ∉ exercise21PoleSet a := hz.2
  have hz1 : z ≠ (1 : ℂ) := by
    intro hz1
    exact hz_off (by simp [exercise21PoleSet, hz1])
  have hz_ai : z ≠ (a : ℂ) * Complex.I := by
    intro hz_ai
    exact hz_off (by simp [exercise21PoleSet, hz_ai])
  have hz_neg_ai : z ≠ -((a : ℂ) * Complex.I) := by
    intro hz_neg_ai
    exact hz_off (by simp [exercise21PoleSet, hz_neg_ai])
  have hintegrand :
      DifferentiableAt ℂ (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹)) z :=
    exercise21_integrand_differentiableAt_of_mem_slitPlane_off_poles a hz_slit hz_off
  have hrealPole :
      DifferentiableAt ℂ
        (fun w ↦ exercise21RealPoleCoeff a / (w - 1)) z := by
    -- The real-pole term is a constant multiple of the holomorphic reciprocal kernel off `z = 1`.
    have hkernel : DifferentiableAt ℂ (fun w : ℂ ↦ (w - 1)⁻¹) z := by
      exact (differentiableAt_id.sub_const (1 : ℂ)).inv (sub_ne_zero.mpr hz1)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hkernel.const_mul (exercise21RealPoleCoeff a)
  have hposImagPole :
      DifferentiableAt ℂ
        (fun w ↦
          exercise21PosImagPoleCoeff a /
            (w - (a : ℂ) * Complex.I)) z := by
    -- The same reciprocal-kernel argument works at the pole `a i`.
    have hkernel : DifferentiableAt ℂ (fun w : ℂ ↦ (w - (a : ℂ) * Complex.I)⁻¹) z := by
      exact (differentiableAt_id.sub_const ((a : ℂ) * Complex.I)).inv (sub_ne_zero.mpr hz_ai)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hkernel.const_mul (exercise21PosImagPoleCoeff a)
  have hnegImagPole :
      DifferentiableAt ℂ
        (fun w ↦
          exercise21NegImagPoleCoeff a /
            (w + (a : ℂ) * Complex.I)) z := by
    -- Rewrite the denominator as `w - (-a i)` so the off-pole reciprocal lemma applies unchanged.
    have hkernel : DifferentiableAt ℂ (fun w : ℂ ↦ (w - (-((a : ℂ) * Complex.I)))⁻¹) z := by
      exact (differentiableAt_id.sub_const (-((a : ℂ) * Complex.I))).inv
        (sub_ne_zero.mpr hz_neg_ai)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hkernel.const_mul (exercise21NegImagPoleCoeff a)
  have hregular :
      DifferentiableAt ℂ (exercise21RegularPart a) z := by
    -- Combine the punctured holomorphy of the integrand with the three holomorphic kernel terms.
    have hsub1 :
        DifferentiableAt ℂ
          (fun w ↦
            (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹) -
              exercise21RealPoleCoeff a / (w - 1)) z :=
      hintegrand.sub hrealPole
    have hsub2 :
        DifferentiableAt ℂ
          (fun w ↦
            (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹) -
              exercise21RealPoleCoeff a / (w - 1) -
                exercise21PosImagPoleCoeff a / (w - (a : ℂ) * Complex.I)) z :=
      hsub1.sub hposImagPole
    have hsub3 :
        DifferentiableAt ℂ (exercise21RegularPart a) z := by
      change DifferentiableAt ℂ
        (fun w ↦
          (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹) -
            exercise21RealPoleCoeff a / (w - 1) -
              exercise21PosImagPoleCoeff a / (w - (a : ℂ) * Complex.I) -
                exercise21NegImagPoleCoeff a / (w + (a : ℂ) * Complex.I)) z
      exact hsub2.sub hnegImagPole
    exact hsub3
  exact hregular.differentiableWithinAt

/-- Helper for Exercise 21: a sufficiently small circle around `1` realizes the residue
coefficient `1 / (1 + a^2)` while staying away from the imaginary poles. -/
lemma exercise21_real_pole_localResidueCircle
    {K : Set ℂ} {ρ : ℝ} (a : ℝ)
    (hρ : 0 < ρ)
    (hK : Metric.closedBall (1 : ℂ) ρ ⊆ interior K)
    (hD :
      Metric.closedBall (1 : ℂ) ρ ⊆
        Complex.slitPlane \ ({(a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)} : Set ℂ)) :
    LocalResidueCircle
      K
      Complex.slitPlane
      (fun z ↦ (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹))
      (1 : ℂ)
      (exercise21RealPoleCoeff a) := by
  let D : Set ℂ := Complex.slitPlane \ ({(a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)} : Set ℂ)
  let g : ℂ → ℂ := fun z ↦ (((z ^ 2 + (a : ℂ) ^ 2) * dslope Complex.log 1 z)⁻¹)
  have hdslope :
      DifferentiableOn ℂ (dslope Complex.log 1) Complex.slitPlane := by
    -- The removable singularity theorem turns the principal logarithm into a holomorphic divided
    -- difference on the whole slit plane.
    exact
      (Complex.differentiableOn_dslope
        ((Complex.isOpen_slitPlane.mem_nhds
          (by simp [Complex.mem_slitPlane_iff] : (1 : ℂ) ∈ Complex.slitPlane)))).2
        exercise21_log_differentiableOn_slitPlane
  have hg : DifferentiableOn ℂ g D := by
    intro z hz
    have hz_slit : z ∈ Complex.slitPlane := hz.1
    have hz_ai : z ≠ (a : ℂ) * Complex.I := by
      intro h
      exact hz.2 (by simp [h])
    have hz_neg_ai : z ≠ -((a : ℂ) * Complex.I) := by
      intro h
      exact hz.2 (by simp [h])
    have hquad_ne : z ^ 2 + (a : ℂ) ^ 2 ≠ 0 :=
      exercise21_quadratic_ne_zero_of_off_imag_poles a hz_ai hz_neg_ai
    have hdslope_ne : dslope Complex.log 1 z ≠ 0 :=
      exercise21_dslope_log_ne_zero_of_mem_slitPlane hz_slit
    have hdenom_ne : ((z ^ 2 + (a : ℂ) ^ 2) * dslope Complex.log 1 z) ≠ 0 :=
      mul_ne_zero hquad_ne hdslope_ne
    have hquad : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ 2 + (a : ℂ) ^ 2) z := by
      fun_prop
    have hdiff :
        DifferentiableAt ℂ (dslope Complex.log 1) z := by
      exact (hdslope z hz_slit).differentiableAt (Complex.isOpen_slitPlane.mem_nhds hz_slit)
    -- The reciprocal is holomorphic because both factors stay nonzero on the punctured domain.
    simpa [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ((hquad.mul hdiff).inv hdenom_ne).differentiableWithinAt
  have hlocal :
      LocalResidueCircle K D (fun z ↦ g z / (z - (1 : ℂ))) (1 : ℂ) (g 1) :=
    localResidueCircle_div_sub_of_differentiableOn
      (K := K) (D := D) (g := g) (a := (1 : ℂ)) (r := ρ) hρ hK hD hg
  rcases hlocal with ⟨radius, hradius, hballK, hballD, hcircle⟩
  refine ⟨radius, hradius, hballK, ?_, ?_⟩
  · intro z hz
    exact (hballD hz).1
  · have hcongr :
        (∮ z in C((1 : ℂ), radius), (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹)) =
          ∮ z in C((1 : ℂ), radius), g z / (z - (1 : ℂ)) := by
      -- On the whole small circle, the original integrand is already in the standard `/(z-1)`
      -- kernel form.
      refine circleIntegral.integral_congr hradius.le ?_
      intro z hz
      simpa [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        exercise21_integrand_eq_real_pole_kernel a (z := z)
    have hg_one : g 1 = exercise21RealPoleCoeff a := by
      -- Evaluating the divided difference at the center reduces to `log'(1) = 1`.
      have hderiv : deriv Complex.log (1 : ℂ) = 1 := by
        simpa using
          (Complex.hasDerivAt_log
            (by simp [Complex.mem_slitPlane_iff] : (1 : ℂ) ∈ Complex.slitPlane)).deriv
      simp [g, exercise21RealPoleCoeff, dslope_same, hderiv]
    rw [hcongr, hcircle, hg_one]

/-- Helper for Exercise 21: a sufficiently small circle around `a i` realizes the positive
imaginary residue while staying away from the other two poles. -/
lemma exercise21_pos_imag_pole_localResidueCircle
    {K : Set ℂ} {ρ : ℝ} (a : ℝ)
    (hρ : 0 < ρ)
    (hK : Metric.closedBall ((a : ℂ) * Complex.I) ρ ⊆ interior K)
    (hD :
      Metric.closedBall ((a : ℂ) * Complex.I) ρ ⊆
        Complex.slitPlane \ ({(1 : ℂ), -((a : ℂ) * Complex.I)} : Set ℂ)) :
    LocalResidueCircle
      K
      Complex.slitPlane
      (fun z ↦ (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹))
      ((a : ℂ) * Complex.I)
      (exercise21PosImagPoleCoeff a) := by
  let D : Set ℂ := Complex.slitPlane \ ({(1 : ℂ), -((a : ℂ) * Complex.I)} : Set ℂ)
  let g : ℂ → ℂ := fun z ↦ ((((z + (a : ℂ) * Complex.I) * Complex.log z)⁻¹))
  have hg : DifferentiableOn ℂ g D := by
    intro z hz
    have hz_slit : z ∈ Complex.slitPlane := hz.1
    have hz_one : z ≠ (1 : ℂ) := by
      intro h
      exact hz.2 (by simp [h])
    have hz_neg_ai : z ≠ -((a : ℂ) * Complex.I) := by
      intro h
      exact hz.2 (by simp [h])
    have hlog_ne : Complex.log z ≠ 0 :=
      exercise21_log_ne_zero_of_mem_slitPlane_ne_one hz_slit hz_one
    have hfactor_ne : z + (a : ℂ) * Complex.I ≠ 0 := by
      simpa [eq_neg_iff_add_eq_zero] using hz_neg_ai
    have hdenom_ne : ((z + (a : ℂ) * Complex.I) * Complex.log z) ≠ 0 :=
      mul_ne_zero hfactor_ne hlog_ne
    have hfactor : DifferentiableAt ℂ (fun w : ℂ ↦ w + (a : ℂ) * Complex.I) z := by
      fun_prop
    have hlog : DifferentiableAt ℂ Complex.log z := by
      simpa using (Complex.hasDerivAt_log hz_slit).differentiableAt
    -- The pole factor `z - a i` has been split off, leaving a holomorphic coefficient.
    simpa [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ((hfactor.mul hlog).inv hdenom_ne).differentiableWithinAt
  have hlocal :
      LocalResidueCircle
        K D (fun z ↦ g z / (z - (a : ℂ) * Complex.I))
        ((a : ℂ) * Complex.I) (g ((a : ℂ) * Complex.I)) :=
    localResidueCircle_div_sub_of_differentiableOn
      (K := K) (D := D) (g := g) (a := (a : ℂ) * Complex.I) (r := ρ) hρ hK hD hg
  rcases hlocal with ⟨radius, hradius, hballK, hballD, hcircle⟩
  refine ⟨radius, hradius, hballK, ?_, ?_⟩
  · intro z hz
    exact (hballD hz).1
  · have hcongr :
        (∮ z in C((a : ℂ) * Complex.I, radius),
            (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹)) =
          ∮ z in C((a : ℂ) * Complex.I, radius), g z / (z - (a : ℂ) * Complex.I) := by
      -- On the punctured circle, the original integrand is the simple-pole kernel at `a i`.
      refine circleIntegral.integral_congr hradius.le ?_
      intro z hz
      have hz_ne : z ≠ (a : ℂ) * Complex.I := by
        intro h
        have : (0 : ℝ) = radius := by
          simpa [Metric.mem_sphere, Complex.dist_eq, h] using hz
        exact hradius.ne' this.symm
      simpa [g] using exercise21_integrand_eq_pos_imag_pole_kernel a hz_ne
    have hg_ai : g ((a : ℂ) * Complex.I) = exercise21PosImagPoleCoeff a := by
      -- Evaluating the holomorphic coefficient at the pole gives the stated residue.
      have htwo :
          (a : ℂ) * Complex.I + (a : ℂ) * Complex.I = 2 * (a : ℂ) * Complex.I := by
        ring
      simpa [g, exercise21PosImagPoleCoeff, div_eq_mul_inv, htwo]
    rw [hcongr, hcircle, hg_ai]

/-- Helper for Exercise 21: a sufficiently small circle around `-a i` realizes the negative
imaginary residue while staying away from the other two poles. -/
lemma exercise21_neg_imag_pole_localResidueCircle
    {K : Set ℂ} {ρ : ℝ} (a : ℝ)
    (hρ : 0 < ρ)
    (hK : Metric.closedBall (-((a : ℂ) * Complex.I)) ρ ⊆ interior K)
    (hD :
      Metric.closedBall (-((a : ℂ) * Complex.I)) ρ ⊆
        Complex.slitPlane \ ({(1 : ℂ), (a : ℂ) * Complex.I} : Set ℂ)) :
    LocalResidueCircle
      K
      Complex.slitPlane
      (fun z ↦ (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹))
      (-((a : ℂ) * Complex.I))
      (exercise21NegImagPoleCoeff a) := by
  let D : Set ℂ := Complex.slitPlane \ ({(1 : ℂ), (a : ℂ) * Complex.I} : Set ℂ)
  let g : ℂ → ℂ := fun z ↦ ((((z - (a : ℂ) * Complex.I) * Complex.log z)⁻¹))
  have hg : DifferentiableOn ℂ g D := by
    intro z hz
    have hz_slit : z ∈ Complex.slitPlane := hz.1
    have hz_one : z ≠ (1 : ℂ) := by
      intro h
      exact hz.2 (by simp [h])
    have hz_ai : z ≠ (a : ℂ) * Complex.I := by
      intro h
      exact hz.2 (by simp [h])
    have hlog_ne : Complex.log z ≠ 0 :=
      exercise21_log_ne_zero_of_mem_slitPlane_ne_one hz_slit hz_one
    have hfactor_ne : z - (a : ℂ) * Complex.I ≠ 0 := sub_ne_zero.mpr hz_ai
    have hdenom_ne : ((z - (a : ℂ) * Complex.I) * Complex.log z) ≠ 0 :=
      mul_ne_zero hfactor_ne hlog_ne
    have hfactor : DifferentiableAt ℂ (fun w : ℂ ↦ w - (a : ℂ) * Complex.I) z := by
      fun_prop
    have hlog : DifferentiableAt ℂ Complex.log z := by
      simpa using (Complex.hasDerivAt_log hz_slit).differentiableAt
    -- After factoring out `z + a i`, only a holomorphic coefficient remains.
    simpa [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ((hfactor.mul hlog).inv hdenom_ne).differentiableWithinAt
  have hlocal :
      LocalResidueCircle
        K D (fun z ↦ g z / (z + (a : ℂ) * Complex.I))
        (-((a : ℂ) * Complex.I)) (g (-((a : ℂ) * Complex.I))) :=
    by
      simpa [sub_eq_add_neg] using
        (localResidueCircle_div_sub_of_differentiableOn
          (K := K) (D := D) (g := g) (a := -((a : ℂ) * Complex.I)) (r := ρ) hρ hK hD hg)
  rcases hlocal with ⟨radius, hradius, hballK, hballD, hcircle⟩
  refine ⟨radius, hradius, hballK, ?_, ?_⟩
  · intro z hz
    exact (hballD hz).1
  · have hcongr :
        (∮ z in C(-((a : ℂ) * Complex.I), radius),
            (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹)) =
          ∮ z in C(-((a : ℂ) * Complex.I), radius), g z / (z + (a : ℂ) * Complex.I) := by
      -- On the punctured circle, the original integrand is the simple-pole kernel at `-a i`.
      refine circleIntegral.integral_congr hradius.le ?_
      intro z hz
      have hz_ne : z ≠ -((a : ℂ) * Complex.I) := by
        intro h
        have : (0 : ℝ) = radius := by
          simpa [Metric.mem_sphere, Complex.dist_eq, h] using hz
        exact hradius.ne' this.symm
      simpa [g] using exercise21_integrand_eq_neg_imag_pole_kernel a hz_ne
    have hg_neg_ai : g (-((a : ℂ) * Complex.I)) = exercise21NegImagPoleCoeff a := by
      -- The remaining coefficient evaluates to the stated negative residue.
      have htwo :
          -((a : ℂ) * Complex.I) - (a : ℂ) * Complex.I = -(2 * (a : ℂ) * Complex.I) := by
        ring
      simpa [g, exercise21NegImagPoleCoeff, div_eq_mul_inv, htwo, inv_neg]
    rw [hcongr, hcircle, hg_neg_ai]

/-- Helper for Exercise 21: once three small residue circles are chosen around `1`, `a i`, and
`-a i`, the residue theorem hypotheses at all poles can be bundled uniformly. -/
lemma exercise21_localResidueCircle_data
    {K : Set ℂ} (a : ℝ) (ha : 0 < a) {ρ₁ ρ₂ ρ₃ : ℝ}
    (hρ₁ : 0 < ρ₁)
    (hK₁ : Metric.closedBall (1 : ℂ) ρ₁ ⊆ interior K)
    (hD₁ :
      Metric.closedBall (1 : ℂ) ρ₁ ⊆
        Complex.slitPlane \ ({(a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)} : Set ℂ))
    (hρ₂ : 0 < ρ₂)
    (hK₂ : Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆ interior K)
    (hD₂ :
      Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆
        Complex.slitPlane \ ({(1 : ℂ), -((a : ℂ) * Complex.I)} : Set ℂ))
    (hρ₃ : 0 < ρ₃)
    (hK₃ : Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆ interior K)
    (hD₃ :
      Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆
        Complex.slitPlane \ ({(1 : ℂ), (a : ℂ) * Complex.I} : Set ℂ)) :
    ∀ z ∈ exercise21PoleFinset a,
      LocalResidueCircle
        K
        Complex.slitPlane
        (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹))
        z
        (exercise21Residue a z) := by
  have h_ai_ne_one : (a : ℂ) * Complex.I ≠ (1 : ℂ) := by
    intro h
    have him := congrArg Complex.im h
    simpa [ha.ne'] using him
  have h_neg_ai_ne_one : -((a : ℂ) * Complex.I) ≠ (1 : ℂ) := by
    intro h
    have him := congrArg Complex.im h
    simpa [ha.ne'] using him
  have h_ai_ne_neg_ai : (a : ℂ) * Complex.I ≠ -((a : ℂ) * Complex.I) := by
    intro h
    have him := congrArg Complex.im h
    have : a = -a := by simpa using him
    linarith
  have h_neg_ai_ne_ai : -((a : ℂ) * Complex.I) ≠ (a : ℂ) * Complex.I := by
    intro h
    exact h_ai_ne_neg_ai h.symm
  intro z hz
  -- The pole set is exactly the three simple poles handled above.
  simp [exercise21PoleFinset] at hz
  rcases hz with rfl | rfl | rfl
  · simpa [exercise21Residue, h_ai_ne_one, h_neg_ai_ne_one] using
      exercise21_real_pole_localResidueCircle (K := K) (ρ := ρ₁) a hρ₁ hK₁ hD₁
  · simpa [exercise21Residue, h_ai_ne_one, h_ai_ne_neg_ai] using
      exercise21_pos_imag_pole_localResidueCircle (K := K) (ρ := ρ₂) a hρ₂ hK₂ hD₂
  · simpa [exercise21Residue, h_neg_ai_ne_one, h_neg_ai_ne_ai] using
      exercise21_neg_imag_pole_localResidueCircle (K := K) (ρ := ρ₃) a hρ₃ hK₃ hD₃

/-- Helper for Exercise 21: the three explicit local residue circles can be upgraded to isolated
residue circles because each owner closed ball already avoids the other two poles and the
integrand is holomorphic on the punctured slit-plane away from the pole finset. -/
lemma exercise21_isolatedLocalResidueCircle_data
    {K : Set ℂ} (a : ℝ) (ha : 0 < a) {ρ₁ ρ₂ ρ₃ : ℝ}
    (hρ₁ : 0 < ρ₁)
    (hK₁ : Metric.closedBall (1 : ℂ) ρ₁ ⊆ interior K)
    (hD₁ :
      Metric.closedBall (1 : ℂ) ρ₁ ⊆
        Complex.slitPlane \ ({(a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)} : Set ℂ))
    (hρ₂ : 0 < ρ₂)
    (hK₂ : Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆ interior K)
    (hD₂ :
      Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆
        Complex.slitPlane \ ({(1 : ℂ), -((a : ℂ) * Complex.I)} : Set ℂ))
    (hρ₃ : 0 < ρ₃)
    (hK₃ : Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆ interior K)
    (hD₃ :
      Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆
        Complex.slitPlane \ ({(1 : ℂ), (a : ℂ) * Complex.I} : Set ℂ)) :
    ∀ z ∈ exercise21PoleFinset a,
      IsolatedLocalResidueCircle
        K
        Complex.slitPlane
        (exercise21PoleFinset a)
        (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹))
        z
        (exercise21Residue a z) := by
  have h_ai_ne_one : (a : ℂ) * Complex.I ≠ (1 : ℂ) := by
    intro h
    have him := congrArg Complex.im h
    simpa [ha.ne'] using him
  have h_neg_ai_ne_one : -((a : ℂ) * Complex.I) ≠ (1 : ℂ) := by
    intro h
    have him := congrArg Complex.im h
    simpa [ha.ne'] using him
  have h_ai_ne_neg_ai : (a : ℂ) * Complex.I ≠ -((a : ℂ) * Complex.I) := by
    intro h
    have him := congrArg Complex.im h
    have : a = -a := by simpa using him
    linarith
  have h_neg_ai_ne_ai : -((a : ℂ) * Complex.I) ≠ (a : ℂ) * Complex.I := by
    intro h
    exact h_ai_ne_neg_ai h.symm
  intro z hz
  simp [exercise21PoleFinset] at hz
  rcases hz with rfl | rfl | rfl
  · let D : Set ℂ := Complex.slitPlane \ ({(a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)} : Set ℂ)
    let g : ℂ → ℂ := fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * dslope Complex.log 1 w)⁻¹)
    have hdslope :
        DifferentiableOn ℂ (dslope Complex.log 1) Complex.slitPlane := by
      exact
        (Complex.differentiableOn_dslope
          ((Complex.isOpen_slitPlane.mem_nhds
            (by simp [Complex.mem_slitPlane_iff] : (1 : ℂ) ∈ Complex.slitPlane)))).2
          exercise21_log_differentiableOn_slitPlane
    have hg : DifferentiableOn ℂ g D := by
      intro w hw
      have hw_slit : w ∈ Complex.slitPlane := hw.1
      have hw_ai : w ≠ (a : ℂ) * Complex.I := by
        intro h
        exact hw.2 (by simp [h])
      have hw_neg_ai : w ≠ -((a : ℂ) * Complex.I) := by
        intro h
        exact hw.2 (by simp [h])
      have hquad_ne : w ^ 2 + (a : ℂ) ^ 2 ≠ 0 :=
        exercise21_quadratic_ne_zero_of_off_imag_poles a hw_ai hw_neg_ai
      have hdslope_ne : dslope Complex.log 1 w ≠ 0 :=
        exercise21_dslope_log_ne_zero_of_mem_slitPlane hw_slit
      have hdenom_ne : ((w ^ 2 + (a : ℂ) ^ 2) * dslope Complex.log 1 w) ≠ 0 :=
        mul_ne_zero hquad_ne hdslope_ne
      have hquad : DifferentiableAt ℂ (fun u : ℂ ↦ u ^ 2 + (a : ℂ) ^ 2) w := by
        fun_prop
      have hdiff :
          DifferentiableAt ℂ (dslope Complex.log 1) w := by
        exact (hdslope w hw_slit).differentiableAt (Complex.isOpen_slitPlane.mem_nhds hw_slit)
      simpa [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        ((hquad.mul hdiff).inv hdenom_ne).differentiableWithinAt
    have havoid :
        ∀ w ∈ exercise21PoleFinset a, w ≠ (1 : ℂ) → w ∉ Metric.closedBall (1 : ℂ) ρ₁ := by
      intro w hw hwz hwBall
      simp [exercise21PoleFinset] at hw
      rcases hw with rfl | rfl | rfl
      · exact hwz rfl
      · exact (hD₁ hwBall).2 (by simp)
      · exact (hD₁ hwBall).2 (by simp)
    have hdiff :
        DifferentiableOn ℂ
          (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹))
          (Metric.ball (1 : ℂ) ρ₁ \ ({(1 : ℂ)} : Set ℂ)) := by
      refine (exercise21_integrand_differentiableOn_slitPlane_off_poles_finset a).mono ?_
      intro w hw
      have hwClosed : w ∈ Metric.closedBall (1 : ℂ) ρ₁ := Metric.ball_subset_closedBall hw.1
      refine ⟨(hD₁ hwClosed).1, ?_⟩
      intro hwPole
      simp [exercise21PoleFinset] at hwPole
      rcases hwPole with hw1 | hwai | hwneg
      · exact hw.2 hw1
      · exact (hD₁ hwClosed).2 (by simp [hwai])
      · exact (hD₁ hwClosed).2 (by simp [hwneg])
    have hcongr :
        (∮ w in C((1 : ℂ), ρ₁), (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹)) =
          ∮ w in C((1 : ℂ), ρ₁), g w / (w - (1 : ℂ)) := by
      refine circleIntegral.integral_congr hρ₁.le ?_
      intro w hw
      simpa [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        exercise21_integrand_eq_real_pole_kernel a (z := w)
    have hcircle_kernel :
        ∮ w in C((1 : ℂ), ρ₁), g w / (w - (1 : ℂ)) =
          (2 * Real.pi * Complex.I : ℂ) * g (1 : ℂ) := by
      have hg_ball : DifferentiableOn ℂ g (Metric.closedBall (1 : ℂ) ρ₁) := hg.mono hD₁
      have hcenter_ball : (1 : ℂ) ∈ Metric.ball (1 : ℂ) ρ₁ := Metric.mem_ball_self hρ₁
      simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
        hg_ball.circleIntegral_sub_inv_smul hcenter_ball
    have hg_one : g (1 : ℂ) = exercise21RealPoleCoeff a := by
      have hderiv : deriv Complex.log (1 : ℂ) = 1 := by
        simpa using
          (Complex.hasDerivAt_log
            (by simp [Complex.mem_slitPlane_iff] : (1 : ℂ) ∈ Complex.slitPlane)).deriv
      simp [g, exercise21RealPoleCoeff, dslope_same, hderiv]
    refine ⟨ρ₁, hρ₁, hK₁, ?_, havoid, hdiff, ?_⟩
    · intro w hw
      exact (hD₁ hw).1
    · rw [hcongr, hcircle_kernel, hg_one]
      simpa [exercise21Residue, h_ai_ne_one, h_neg_ai_ne_one]
  · let D : Set ℂ := Complex.slitPlane \ ({(1 : ℂ), -((a : ℂ) * Complex.I)} : Set ℂ)
    let g : ℂ → ℂ := fun w ↦ (((w + (a : ℂ) * Complex.I) * Complex.log w)⁻¹)
    have hg : DifferentiableOn ℂ g D := by
      intro w hw
      have hw_slit : w ∈ Complex.slitPlane := hw.1
      have hw_one : w ≠ (1 : ℂ) := by
        intro h
        exact hw.2 (by simp [h])
      have hw_neg_ai : w ≠ -((a : ℂ) * Complex.I) := by
        intro h
        exact hw.2 (by simp [h])
      have hlog_ne : Complex.log w ≠ 0 :=
        exercise21_log_ne_zero_of_mem_slitPlane_ne_one hw_slit hw_one
      have hfactor_ne : w + (a : ℂ) * Complex.I ≠ 0 := by
        simpa [eq_neg_iff_add_eq_zero] using hw_neg_ai
      have hdenom_ne : ((w + (a : ℂ) * Complex.I) * Complex.log w) ≠ 0 :=
        mul_ne_zero hfactor_ne hlog_ne
      have hfactor : DifferentiableAt ℂ (fun u : ℂ ↦ u + (a : ℂ) * Complex.I) w := by
        fun_prop
      have hlog : DifferentiableAt ℂ Complex.log w := by
        simpa using (Complex.hasDerivAt_log hw_slit).differentiableAt
      simpa [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        ((hfactor.mul hlog).inv hdenom_ne).differentiableWithinAt
    have havoid :
        ∀ w ∈ exercise21PoleFinset a, w ≠ (a : ℂ) * Complex.I →
          w ∉ Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ := by
      intro w hw hwz hwBall
      simp [exercise21PoleFinset] at hw
      rcases hw with rfl | rfl | rfl
      · exact (hD₂ hwBall).2 (by simp)
      · exact hwz rfl
      · exact (hD₂ hwBall).2 (by simp)
    have hdiff :
        DifferentiableOn ℂ
          (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹))
          (Metric.ball ((a : ℂ) * Complex.I) ρ₂ \ ({(a : ℂ) * Complex.I} : Set ℂ)) := by
      refine (exercise21_integrand_differentiableOn_slitPlane_off_poles_finset a).mono ?_
      intro w hw
      have hwClosed :
          w ∈ Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ := Metric.ball_subset_closedBall hw.1
      refine ⟨(hD₂ hwClosed).1, ?_⟩
      intro hwPole
      simp [exercise21PoleFinset] at hwPole
      rcases hwPole with hw1 | hwai | hwneg
      · exact (hD₂ hwClosed).2 (by simp [hw1])
      · exact hw.2 hwai
      · exact (hD₂ hwClosed).2 (by simp [hwneg])
    have hcongr :
        (∮ w in C((a : ℂ) * Complex.I, ρ₂),
            (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹)) =
          ∮ w in C((a : ℂ) * Complex.I, ρ₂), g w / (w - (a : ℂ) * Complex.I) := by
      refine circleIntegral.integral_congr hρ₂.le ?_
      intro w hw
      have hw_ne : w ≠ (a : ℂ) * Complex.I := by
        intro h
        have : (0 : ℝ) = ρ₂ := by
          simpa [Metric.mem_sphere, Complex.dist_eq, h] using hw
        exact hρ₂.ne' this.symm
      simpa [g] using exercise21_integrand_eq_pos_imag_pole_kernel a hw_ne
    have hcircle_kernel :
        ∮ w in C((a : ℂ) * Complex.I, ρ₂), g w / (w - (a : ℂ) * Complex.I) =
          (2 * Real.pi * Complex.I : ℂ) * g ((a : ℂ) * Complex.I) := by
      have hg_ball :
          DifferentiableOn ℂ g (Metric.closedBall ((a : ℂ) * Complex.I) ρ₂) := hg.mono hD₂
      have hcenter_ball :
          (a : ℂ) * Complex.I ∈ Metric.ball ((a : ℂ) * Complex.I) ρ₂ :=
        Metric.mem_ball_self hρ₂
      simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
        hg_ball.circleIntegral_sub_inv_smul hcenter_ball
    have hg_ai : g ((a : ℂ) * Complex.I) = exercise21PosImagPoleCoeff a := by
      have htwo :
          (a : ℂ) * Complex.I + (a : ℂ) * Complex.I = 2 * (a : ℂ) * Complex.I := by
        ring
      simpa [g, exercise21PosImagPoleCoeff, div_eq_mul_inv, htwo]
    refine ⟨ρ₂, hρ₂, hK₂, ?_, havoid, hdiff, ?_⟩
    · intro w hw
      exact (hD₂ hw).1
    · rw [hcongr, hcircle_kernel, hg_ai]
      simpa [exercise21Residue, h_ai_ne_one, h_ai_ne_neg_ai]
  · let D : Set ℂ := Complex.slitPlane \ ({(1 : ℂ), (a : ℂ) * Complex.I} : Set ℂ)
    let g : ℂ → ℂ := fun w ↦ (((w - (a : ℂ) * Complex.I) * Complex.log w)⁻¹)
    have hg : DifferentiableOn ℂ g D := by
      intro w hw
      have hw_slit : w ∈ Complex.slitPlane := hw.1
      have hw_one : w ≠ (1 : ℂ) := by
        intro h
        exact hw.2 (by simp [h])
      have hw_ai : w ≠ (a : ℂ) * Complex.I := by
        intro h
        exact hw.2 (by simp [h])
      have hlog_ne : Complex.log w ≠ 0 :=
        exercise21_log_ne_zero_of_mem_slitPlane_ne_one hw_slit hw_one
      have hfactor_ne : w - (a : ℂ) * Complex.I ≠ 0 := sub_ne_zero.mpr hw_ai
      have hdenom_ne : ((w - (a : ℂ) * Complex.I) * Complex.log w) ≠ 0 :=
        mul_ne_zero hfactor_ne hlog_ne
      have hfactor : DifferentiableAt ℂ (fun u : ℂ ↦ u - (a : ℂ) * Complex.I) w := by
        fun_prop
      have hlog : DifferentiableAt ℂ Complex.log w := by
        simpa using (Complex.hasDerivAt_log hw_slit).differentiableAt
      simpa [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        ((hfactor.mul hlog).inv hdenom_ne).differentiableWithinAt
    have havoid :
        ∀ w ∈ exercise21PoleFinset a, w ≠ -((a : ℂ) * Complex.I) →
          w ∉ Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ := by
      intro w hw hwz hwBall
      simp [exercise21PoleFinset] at hw
      rcases hw with rfl | rfl | rfl
      · exact (hD₃ hwBall).2 (by simp)
      · exact (hD₃ hwBall).2 (by simp)
      · exact hwz rfl
    have hdiff :
        DifferentiableOn ℂ
          (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹))
          (Metric.ball (-((a : ℂ) * Complex.I)) ρ₃ \ ({-((a : ℂ) * Complex.I)} : Set ℂ)) := by
      refine (exercise21_integrand_differentiableOn_slitPlane_off_poles_finset a).mono ?_
      intro w hw
      have hwClosed :
          w ∈ Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ := Metric.ball_subset_closedBall hw.1
      refine ⟨(hD₃ hwClosed).1, ?_⟩
      intro hwPole
      simp [exercise21PoleFinset] at hwPole
      rcases hwPole with hw1 | hwai | hwneg
      · exact (hD₃ hwClosed).2 (by simp [hw1])
      · exact (hD₃ hwClosed).2 (by simp [hwai])
      · exact hw.2 hwneg
    have hcongr :
        (∮ w in C(-((a : ℂ) * Complex.I), ρ₃),
            (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹)) =
          ∮ w in C(-((a : ℂ) * Complex.I), ρ₃), g w / (w + (a : ℂ) * Complex.I) := by
      refine circleIntegral.integral_congr hρ₃.le ?_
      intro w hw
      have hw_ne : w ≠ -((a : ℂ) * Complex.I) := by
        intro h
        have : (0 : ℝ) = ρ₃ := by
          simpa [Metric.mem_sphere, Complex.dist_eq, h] using hw
        exact hρ₃.ne' this.symm
      simpa [g] using exercise21_integrand_eq_neg_imag_pole_kernel a hw_ne
    have hcircle_kernel :
        ∮ w in C(-((a : ℂ) * Complex.I), ρ₃), g w / (w + (a : ℂ) * Complex.I) =
          (2 * Real.pi * Complex.I : ℂ) * g (-((a : ℂ) * Complex.I)) := by
      have hg_ball :
          DifferentiableOn ℂ g (Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃) := hg.mono hD₃
      have hcenter_ball :
          -((a : ℂ) * Complex.I) ∈ Metric.ball (-((a : ℂ) * Complex.I)) ρ₃ :=
        Metric.mem_ball_self hρ₃
      simpa [sub_eq_add_neg, div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
        hg_ball.circleIntegral_sub_inv_smul hcenter_ball
    have hg_neg_ai : g (-((a : ℂ) * Complex.I)) = exercise21NegImagPoleCoeff a := by
      have htwo :
          -((a : ℂ) * Complex.I) - (a : ℂ) * Complex.I = -(2 * (a : ℂ) * Complex.I) := by
        ring
      simpa [g, exercise21NegImagPoleCoeff, div_eq_mul_inv, htwo, inv_neg]
    refine ⟨ρ₃, hρ₃, hK₃, ?_, havoid, hdiff, ?_⟩
    · intro w hw
      exact (hD₃ hw).1
    · rw [hcongr, hcircle_kernel, hg_neg_ai]
      simpa [exercise21Residue, h_neg_ai_ne_one, h_neg_ai_ne_ai]
