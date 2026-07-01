import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open Filter
open scoped Real
open scoped Topology

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the improper-integral notation and complex-expression surface were checked against local
-- section precedent and mathlib's Gamma/improper-integral owners:
-- `integral_rpow_mul_exp_neg_mul_rpow`, `integral_exp_mul_complex_Ioi`,
-- `Complex.exp_add_mul_I`, and `integral_re` / `integral_im`.

/-- Helper for Exercise 24: the norm of the complex Laplace integrand is the expected real
decaying weight. -/
lemma norm_pow_mul_exp_neg_mul_complex
    (p q : ℝ) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ m * Complex.exp (((-p : ℂ) + (q : ℂ) * Complex.I) * (x : ℂ))‖ =
      x ^ m * Real.exp (-p * x) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx, Complex.norm_exp]
  simp [Complex.mul_re, mul_comm]

/-- Helper for Exercise 24: the polynomial-exponential complex integrand tends to `0` at `+∞`. -/
lemma tendsto_zero_atTop_pow_mul_complex_exp
    (p q : ℝ) (m : ℕ) (hp : 0 < p) :
    Tendsto
      (fun x : ℝ ↦ (x : ℂ) ^ m * Complex.exp (((-p : ℂ) + (q : ℂ) * Complex.I) * (x : ℂ)))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine Tendsto.congr' ?_ (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero m p hp)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [norm_pow_mul_exp_neg_mul_complex p q m hx, Real.rpow_natCast]

/-- Helper for Exercise 24: the reciprocal Laplace factor matches the textbook closed form. -/
lemma laplace_factor_eq
    (p q : ℝ) (hp : 0 < p) :
    -((((-p : ℂ) + (q : ℂ) * Complex.I))⁻¹) =
      (((p : ℂ) + (q : ℂ) * Complex.I) / (p ^ 2 + q ^ 2)) := by
  -- Route correction: isolate the reciprocal algebra completely before the recurrence, so the
  -- integration-by-parts proof never has to normalize `-a⁻¹` inline.
  have hnorm : Complex.normSq (((-p : ℂ) + (q : ℂ) * Complex.I)) = p ^ 2 + q ^ 2 := by
    simpa [pow_two] using Complex.normSq_add_mul_I (-p) q
  -- Expand the inverse through `inv_def`; after substituting the norm square, only commutativity
  -- of the two summands remains.
  rw [Complex.inv_def, hnorm]
  simp [div_eq_mul_inv, add_mul, mul_assoc, mul_comm, add_comm]

/-- Helper for Exercise 24: the complex Laplace integrand has the canonical `u + v I` expansion
used for the cosine and sine projections. -/
lemma complex_laplace_integrand_eq
    (p q : ℝ) (m : ℕ) (x : ℝ) :
    (x : ℂ) ^ m * Complex.exp (((-p : ℂ) + (q : ℂ) * Complex.I) * (x : ℂ)) =
      ((x ^ m * Real.exp (-p * x) * Real.cos (q * x) : ℝ) : ℂ) +
        (((x ^ m * Real.exp (-p * x) * Real.sin (q * x) : ℝ) : ℂ) * Complex.I) := by
  -- Rewrite the exponent into the canonical `u + v I` form used by `Complex.exp_add_mul_I`.
  calc
    (x : ℂ) ^ m * Complex.exp (((-p : ℂ) + (q : ℂ) * Complex.I) * (x : ℂ))
        = ((x ^ m : ℝ) : ℂ) *
            (((Real.exp (-p * x) : ℝ) : ℂ) *
              (((Real.cos (q * x) : ℝ) : ℂ) + ((Real.sin (q * x) : ℝ) : ℂ) * Complex.I)) := by
            rw [show (((-p : ℂ) + (q : ℂ) * Complex.I) * (x : ℂ)) =
                (((-p * x : ℝ) : ℂ) + ((q * x : ℝ) : ℂ) * Complex.I) by
                simp [mul_add, mul_comm, mul_left_comm, add_comm]]
            rw [Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
              ← Complex.ofReal_sin]
            simp [Complex.ofReal_pow]
    -- Regroup the real scalar factors so the result is literally `u + v I`.
    _ = ((x ^ m * Real.exp (-p * x) * Real.cos (q * x) : ℝ) : ℂ) +
          (((x ^ m * Real.exp (-p * x) * Real.sin (q * x) : ℝ) : ℂ) * Complex.I) := by
          simp [mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm]

/-- Helper for Exercise 24: the real part of the complex Laplace integrand is the cosine
integrand. -/
lemma complex_laplace_integrand_re
    (p q : ℝ) (n : ℕ) (x : ℝ) :
    Complex.re
        ((x : ℂ) ^ (n - 1) * Complex.exp (((-p : ℂ) + (q : ℂ) * Complex.I) * (x : ℂ))) =
      x ^ (n - 1) * Real.exp (-p * x) * Real.cos (q * x) := by
  -- Apply `Complex.re` to the canonical `u + v I` expansion and collapse the zero terms.
  rw [complex_laplace_integrand_eq p q (n - 1) x]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, sub_eq_add_neg, mul_zero, zero_mul,
    zero_add]
  ring

/-- Helper for Exercise 24: the imaginary part of the complex Laplace integrand is the sine
integrand. -/
lemma complex_laplace_integrand_im
    (p q : ℝ) (n : ℕ) (x : ℝ) :
    Complex.im
        ((x : ℂ) ^ (n - 1) * Complex.exp (((-p : ℂ) + (q : ℂ) * Complex.I) * (x : ℂ))) =
      x ^ (n - 1) * Real.exp (-p * x) * Real.sin (q * x) := by
  -- Apply `Complex.im` to the same `u + v I` expansion and keep only the imaginary contribution.
  rw [complex_laplace_integrand_eq p q (n - 1) x]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, add_zero, zero_add]
  ring

/-- Helper for Exercise 24: taking the real part of a real scalar multiple divided by a real
denominator pulls the scalar and denominator outside. -/
lemma complex_scalar_re_div
    (a d : ℝ) (z : ℂ) :
    Complex.re (((a : ℂ) * z) / d) = a * Complex.re z / d := by
  -- Split on the degenerate denominator once; away from `d = 0`, the expression is a purely real
  -- scalar multiple of `re z`.
  by_cases hd : d = 0
  · simp [hd]
  · simp [div_eq_mul_inv, Complex.mul_re, Complex.mul_im, hd, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Exercise 24: taking the imaginary part of a real scalar multiple divided by a real
denominator pulls the scalar and denominator outside. -/
lemma complex_scalar_im_div
    (a d : ℝ) (z : ℂ) :
    Complex.im (((a : ℂ) * z) / d) = a * Complex.im z / d := by
  -- The same scalar-denominator normalization works for the imaginary projection.
  by_cases hd : d = 0
  · simp [hd]
  · simp [div_eq_mul_inv, Complex.mul_re, Complex.mul_im, hd, mul_comm, mul_left_comm, mul_assoc]

/-- Core complex-valued Laplace integral behind Exercise 24. -/
theorem integrableOn_pow_pred_mul_exp_neg_mul_complex
    (p q : ℝ) (n : ℕ) (hp : 0 < p) :
    IntegrableOn
      (fun x : ℝ ↦
        (x : ℂ) ^ (n - 1) * Complex.exp (((-p : ℂ) + (q : ℂ) * Complex.I) * (x : ℂ)))
      (Set.Ioi (0 : ℝ)) := by
  -- Reduce the complex integrability question to the real norm and compare with the standard
  -- `x^(n-1) * exp (-p x)` integrability criterion on `(0, ∞)`.
  refine (integrable_norm_iff ?_).mp ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · have hs0 : 0 ≤ (((n - 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.zero_le (n - 1)
    have hs : -1 < (((n - 1 : ℕ) : ℝ)) := by
      linarith
    have hmodel :
        IntegrableOn
          (fun x : ℝ ↦ x ^ (((n - 1 : ℕ) : ℝ)) * Real.exp (-p * x ^ (1 : ℝ)))
          (Set.Ioi (0 : ℝ)) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := 1) (s := (((n - 1 : ℕ) : ℝ))) (b := p) hs le_rfl hp
    have hreal :
        IntegrableOn
          (fun x : ℝ ↦ x ^ (n - 1) * Real.exp (-p * x))
          (Set.Ioi (0 : ℝ)) := by
      refine IntegrableOn.congr_fun hmodel ?_ measurableSet_Ioi
      intro x hx
      simp [Real.rpow_natCast, Real.rpow_one]
    refine IntegrableOn.congr_fun hreal ?_ measurableSet_Ioi
    intro x hx
    exact (norm_pow_mul_exp_neg_mul_complex p q (n - 1) (Set.mem_Ioi.mp hx)).symm

/-- Helper for Exercise 24: powers of `x` with positive exponent still tend to `0` from the
right. -/
lemma tendsto_zero_right_complex_pow_succ
    (m : ℕ) :
    Tendsto (fun x : ℝ ↦ (x : ℂ) ^ (m + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- Restrict the ordinary continuity limit at `0` to the right-sided neighborhood filter.
  have hcont : Continuous fun x : ℝ ↦ (x : ℂ) ^ (m + 1) := by
    fun_prop
  have h0 :
      Tendsto (fun x : ℝ ↦ (x : ℂ) ^ (m + 1)) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℂ) ^ (m + 1))) :=
    (hcont.continuousAt : ContinuousAt (fun x : ℝ ↦ (x : ℂ) ^ (m + 1)) (0 : ℝ)).tendsto
  simpa using Tendsto.mono_left h0 nhdsWithin_le_nhds

/-- Helper for Exercise 24: the integration-by-parts boundary term at `0+` vanishes. -/
lemma tendsto_zero_right_pow_succ_mul_exp_div
    (a : ℂ) (m : ℕ) :
    Tendsto
      (fun x : ℝ ↦ (x : ℂ) ^ (m + 1) * (Complex.exp (a * (x : ℂ)) / a))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- Split the boundary term into the vanishing polynomial factor and the continuous exponential
  -- factor, then combine the two limits.
  have hpow : Tendsto (fun x : ℝ ↦ (x : ℂ) ^ (m + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_zero_right_complex_pow_succ m
  have hexp :
      Tendsto (fun x : ℝ ↦ Complex.exp (a * (x : ℂ)) / a) (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.exp (a * (0 : ℂ)) / a)) := by
    have hcont : Continuous fun x : ℝ ↦ Complex.exp (a * (x : ℂ)) / a := by
      fun_prop
    exact Tendsto.mono_left
      ((hcont.continuousAt :
          ContinuousAt (fun x : ℝ ↦ Complex.exp (a * (x : ℂ)) / a) (0 : ℝ)).tendsto)
      nhdsWithin_le_nhds
  simpa using hpow.mul hexp

/-- Helper for Exercise 24: the derivative-side term factors through the lower-order Laplace
integrand. -/
lemma deriv_mul_exp_div_factor
    (a : ℂ) (m : ℕ) (x : ℝ) :
    (((m + 1 : ℂ) * (x : ℂ) ^ m) * (Complex.exp (a * (x : ℂ)) / a)) =
      (((m + 1 : ℂ) * a⁻¹) * ((x : ℂ) ^ m * Complex.exp (a * (x : ℂ)))) := by
  -- Pull the constant reciprocal outside once so the recurrence sees exactly the lower-order
  -- integral from the induction hypothesis.
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 24: the shared complex Laplace integral satisfies the factorial recurrence
in the reciprocal factor `-a⁻¹`. -/
lemma integral_pow_mul_exp_neg_mul_complex_recurrence
    (p q : ℝ) (m : ℕ) (hp : 0 < p) :
    ∫ x in Set.Ioi (0 : ℝ),
        (x : ℂ) ^ m * Complex.exp (((-p : ℂ) + (q : ℂ) * Complex.I) * (x : ℂ)) ∂volume =
      (Nat.factorial m : ℂ) * (-((((-p : ℂ) + (q : ℂ) * Complex.I))⁻¹)) ^ (m + 1) := by
  -- Route correction: keep the source integration-by-parts recurrence with `a = -p + iq`; the
  -- only Lean-specific work is the `0+` boundary limit and the final factorial/power normalization.
  let a : ℂ := ((-p : ℂ) + (q : ℂ) * Complex.I)
  let b : ℂ := -a⁻¹
  have ha : a ≠ 0 := by
    intro h0
    have : -p = 0 := by
      simpa [a] using congrArg Complex.re h0
    linarith
  have hrea : a.re < 0 := by
    simpa [a] using (neg_lt_zero.mpr hp)
  induction m with
  | zero =>
      -- The base case is the standard improper exponential integral on `(0, ∞)`.
      simpa [a, b, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        integral_exp_mul_complex_Ioi (a := a) hrea (0 : ℝ)
  | succ m ih =>
      -- Apply integration by parts with `u(x) = x^(m+1)` and `v(x) = exp(a x) / a`.
      have hu :
          ∀ x ∈ Set.Ioi (0 : ℝ),
            HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ (m + 1)) (((m + 1 : ℂ) * (x : ℂ) ^ m)) x := by
        intro x hx
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (((hasDerivAt_id (x : ℂ)).comp_ofReal).pow (m + 1))
      have hv :
          ∀ x ∈ Set.Ioi (0 : ℝ),
            HasDerivAt
              (fun y : ℝ ↦ Complex.exp (a * (y : ℂ)) / a)
              (Complex.exp (a * (x : ℂ))) x := by
        intro x hx
        have hmul : HasDerivAt (fun y : ℝ ↦ a * (y : ℂ)) a x := by
          simpa only [mul_one] using ((hasDerivAt_id (x : ℂ)).const_mul a).comp_ofReal
        have hexp :
            HasDerivAt (fun y : ℝ ↦ Complex.exp (a * (y : ℂ)))
              (Complex.exp (a * (x : ℂ)) * a) x := by
          exact (Complex.hasDerivAt_exp _).comp x hmul
        have hdiv :
            HasDerivAt (fun y : ℝ ↦ Complex.exp (a * (y : ℂ)) / a)
              ((Complex.exp (a * (x : ℂ)) * a) / a) x :=
          hexp.div_const a
        simpa [ha] using hdiv
      have huv' :
          IntegrableOn
            ((fun x : ℝ ↦ (x : ℂ) ^ (m + 1)) * fun x : ℝ ↦ Complex.exp (a * (x : ℂ)))
            (Set.Ioi (0 : ℝ)) := by
        simpa [a, Pi.mul_def] using
          integrableOn_pow_pred_mul_exp_neg_mul_complex p q (m + 2) hp
      have hbase_integrable :
          IntegrableOn
            (fun x : ℝ ↦ (x : ℂ) ^ m * Complex.exp (a * (x : ℂ)))
            (Set.Ioi (0 : ℝ)) := by
        simpa [a] using integrableOn_pow_pred_mul_exp_neg_mul_complex p q (m + 1) hp
      have hu'v_core :
          IntegrableOn
            (fun x : ℝ ↦ ((m + 1 : ℂ) * a⁻¹) * ((x : ℂ) ^ m * Complex.exp (a * (x : ℂ))))
            (Set.Ioi (0 : ℝ)) := by
        simpa using hbase_integrable.const_mul (((m + 1 : ℂ) * a⁻¹))
      have hu'v :
          IntegrableOn
            ((fun x : ℝ ↦ ((m + 1 : ℂ) * (x : ℂ) ^ m)) *
              fun x : ℝ ↦ Complex.exp (a * (x : ℂ)) / a)
            (Set.Ioi (0 : ℝ)) := by
        -- Rewrite `u' * v` into a constant multiple of the induction-hypothesis integrand.
        refine IntegrableOn.congr_fun hu'v_core ?_ measurableSet_Ioi
        intro x hx
        simpa [Pi.mul_def] using (deriv_mul_exp_div_factor a m x).symm
      have h_zero :
          Tendsto
            ((fun x : ℝ ↦ (x : ℂ) ^ (m + 1)) *
              fun x : ℝ ↦ Complex.exp (a * (x : ℂ)) / a)
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        -- The boundary term at `0+` is exactly the packaged one-sided limit helper.
        simpa [Pi.mul_def] using tendsto_zero_right_pow_succ_mul_exp_div a m
      have h_infty :
          Tendsto
            ((fun x : ℝ ↦ (x : ℂ) ^ (m + 1)) *
              fun x : ℝ ↦ Complex.exp (a * (x : ℂ)) / a)
            atTop (𝓝 0) := by
        -- At `+∞`, multiply the known decay of `x^(m+1) exp(a x)` by the constant `a⁻¹`.
        simpa [a, Pi.mul_def, div_eq_mul_inv, mul_assoc] using
          (tendsto_zero_atTop_pow_mul_complex_exp p q (m + 1) hp).mul_const a⁻¹
      have hparts :
          ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (m + 1) * Complex.exp (a * (x : ℂ)) ∂volume =
            0 - 0 -
              ∫ x in Set.Ioi (0 : ℝ),
                (((m + 1 : ℂ) * (x : ℂ) ^ m) * (Complex.exp (a * (x : ℂ)) / a)) ∂volume := by
        -- This is the exact source recurrence `I_{m+1} = - ∫ u'v`.
        simpa [Pi.mul_def] using
          (integral_Ioi_mul_deriv_eq_deriv_mul
            (a := (0 : ℝ))
            (u := fun x : ℝ ↦ (x : ℂ) ^ (m + 1))
            (u' := fun x : ℝ ↦ ((m + 1 : ℂ) * (x : ℂ) ^ m))
            (v := fun x : ℝ ↦ Complex.exp (a * (x : ℂ)) / a)
            (v' := fun x : ℝ ↦ Complex.exp (a * (x : ℂ)))
            hu hv huv' hu'v h_zero h_infty)
      have hfactor :
          ∫ x in Set.Ioi (0 : ℝ),
              (((m + 1 : ℂ) * (x : ℂ) ^ m) * (Complex.exp (a * (x : ℂ)) / a)) ∂volume =
            ((m + 1 : ℂ) * a⁻¹) *
              ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ m * Complex.exp (a * (x : ℂ)) ∂volume := by
        -- Pull the constant factor outside after the pointwise rewrite is stabilized.
        calc
          ∫ x in Set.Ioi (0 : ℝ),
              (((m + 1 : ℂ) * (x : ℂ) ^ m) * (Complex.exp (a * (x : ℂ)) / a)) ∂volume
            = ∫ x in Set.Ioi (0 : ℝ),
                (((m + 1 : ℂ) * a⁻¹) * ((x : ℂ) ^ m * Complex.exp (a * (x : ℂ)))) ∂volume := by
                  refine integral_congr_ae ?_
                  filter_upwards with x
                  rw [deriv_mul_exp_div_factor]
          _ = ((m + 1 : ℂ) * a⁻¹) *
                ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ m * Complex.exp (a * (x : ℂ)) ∂volume := by
                  rw [integral_const_mul]
      have ih' :
          ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ m * Complex.exp (a * (x : ℂ)) ∂volume =
            (Nat.factorial m : ℂ) * b ^ (m + 1) := by
        simpa [a, b] using ih
      calc
        ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (m + 1) * Complex.exp (((-p : ℂ) + (q : ℂ) * Complex.I) * (x : ℂ)) ∂volume
          = ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (m + 1) * Complex.exp (a * (x : ℂ)) ∂volume := by
              simp [a]
        _ = 0 - 0 -
              ∫ x in Set.Ioi (0 : ℝ),
                (((m + 1 : ℂ) * (x : ℂ) ^ m) * (Complex.exp (a * (x : ℂ)) / a)) ∂volume := hparts
        _ = -(((m + 1 : ℂ) * a⁻¹) *
              ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ m * Complex.exp (a * (x : ℂ)) ∂volume) := by
              rw [hfactor]
              simp
        _ = -(((m + 1 : ℂ) * a⁻¹) * ((Nat.factorial m : ℂ) * b ^ (m + 1))) := by
              rw [ih']
        _ = (((m + 1 : ℂ) * b) * ((Nat.factorial m : ℂ) * b ^ (m + 1))) := by
              simp [b, mul_assoc]
        _ = (Nat.factorial (m + 1) : ℂ) * b ^ (m + 2) := by
              rw [Nat.factorial_succ, Nat.cast_mul]
              simp [pow_succ', mul_assoc, mul_left_comm, mul_comm]
        _ = (Nat.factorial (m + 1) : ℂ) *
              (-((((-p : ℂ) + (q : ℂ) * Complex.I))⁻¹)) ^ (m + 2) := by
              simp [a, b]

/-- Core complex-valued Laplace integral behind Exercise 24. -/
theorem integral_pow_pred_mul_exp_neg_mul_complex
    (p q : ℝ) (n : ℕ) (hp : 0 < p) (hn : 1 ≤ n) :
    ∫ x in Set.Ioi (0 : ℝ),
        (x : ℂ) ^ (n - 1) * Complex.exp (((-p : ℂ) + (q : ℂ) * Complex.I) * (x : ℂ)) ∂volume =
      ((Nat.factorial (n - 1) : ℂ) * (((p : ℂ) + (q : ℂ) * Complex.I) ^ n)) /
        (p ^ 2 + q ^ 2) ^ n := by
  -- Use the recurrence theorem first, and only then normalize the single reciprocal factor.
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hrec := integral_pow_mul_exp_neg_mul_complex_recurrence p q m hp
  rw [laplace_factor_eq p q hp, div_pow] at hrec
  simpa [Nat.add_comm, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hrec

-- The textbook assumes `q > 0`, but the formulas only depend on the oscillatory parameter `q`
-- itself, so no positivity hypothesis on `q` is needed in the public API.

/-- Exercise 24 (1): for a real number `p > 0`, a real number `q`, and a natural number `n ≥ 1`,
`∫_0^∞ x^(n-1) e^(-p x) cos(q x) dx = (n - 1)! * Re((p + i q)^n) / (p^2 + q^2)^n`. -/
theorem integral_pow_pred_mul_exp_neg_mul_cos
    (p q : ℝ) (n : ℕ) (hp : 0 < p) (hn : 1 ≤ n) :
    ∫ x in Set.Ioi (0 : ℝ), x ^ (n - 1) * Real.exp (-p * x) * Real.cos (q * x) ∂volume =
      (Nat.factorial (n - 1) : ℝ) * Complex.re (((p : ℂ) + (q : ℂ) * Complex.I) ^ n) /
        (p ^ 2 + q ^ 2) ^ n := by
  -- Project the shared complex integral to its real part after rewriting the integrand pointwise.
  have hf := integrableOn_pow_pred_mul_exp_neg_mul_complex p q n hp
  calc
    ∫ x in Set.Ioi (0 : ℝ), x ^ (n - 1) * Real.exp (-p * x) * Real.cos (q * x) ∂volume
      = ∫ x in Set.Ioi (0 : ℝ),
          Complex.re ((x : ℂ) ^ (n - 1) * Complex.exp (((-p : ℂ) + (q : ℂ) * Complex.I) * (x : ℂ))) ∂volume := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [complex_laplace_integrand_re]
    -- Commute `Complex.re` through the set integral using the integrability already proved.
    _ = Complex.re
          (∫ x in Set.Ioi (0 : ℝ),
            (x : ℂ) ^ (n - 1) * Complex.exp (((-p : ℂ) + (q : ℂ) * Complex.I) * (x : ℂ)) ∂volume) := by
            exact integral_re hf
    -- Substitute the shared complex-valued formula before normalizing the real scalar factor.
    _ = Complex.re
          (((Nat.factorial (n - 1) : ℂ) * (((p : ℂ) + (q : ℂ) * Complex.I) ^ n)) /
            (p ^ 2 + q ^ 2) ^ n) := by
            rw [integral_pow_pred_mul_exp_neg_mul_complex p q n hp hn]
    _ = (Nat.factorial (n - 1) : ℝ) * Complex.re (((p : ℂ) + (q : ℂ) * Complex.I) ^ n) /
          (p ^ 2 + q ^ 2) ^ n := by
            have hpow : ((((p ^ 2 + q ^ 2) ^ n : ℝ) : ℂ)) = (↑p ^ 2 + ↑q ^ 2) ^ n := by
              simp [Complex.ofReal_add, Complex.ofReal_pow]
            rw [← hpow]
            exact complex_scalar_re_div (Nat.factorial (n - 1)) ((p ^ 2 + q ^ 2) ^ n)
              (((p : ℂ) + (q : ℂ) * Complex.I) ^ n)

/-- Exercise 24 (2): for a real number `p > 0`, a real number `q`, and a natural number `n ≥ 1`,
`∫_0^∞ x^(n-1) e^(-p x) sin(q x) dx = (n - 1)! * Im((p + i q)^n) / (p^2 + q^2)^n`. -/
theorem integral_pow_pred_mul_exp_neg_mul_sin
    (p q : ℝ) (n : ℕ) (hp : 0 < p) (hn : 1 ≤ n) :
    ∫ x in Set.Ioi (0 : ℝ), x ^ (n - 1) * Real.exp (-p * x) * Real.sin (q * x) ∂volume =
      (Nat.factorial (n - 1) : ℝ) * Complex.im (((p : ℂ) + (q : ℂ) * Complex.I) ^ n) /
        (p ^ 2 + q ^ 2) ^ n := by
  -- The sine identity is the imaginary-part projection of the same complex Laplace formula.
  have hf := integrableOn_pow_pred_mul_exp_neg_mul_complex p q n hp
  calc
    ∫ x in Set.Ioi (0 : ℝ), x ^ (n - 1) * Real.exp (-p * x) * Real.sin (q * x) ∂volume
      = ∫ x in Set.Ioi (0 : ℝ),
          Complex.im ((x : ℂ) ^ (n - 1) * Complex.exp (((-p : ℂ) + (q : ℂ) * Complex.I) * (x : ℂ))) ∂volume := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [complex_laplace_integrand_im]
    -- Commute `Complex.im` through the set integral before substituting the closed form.
    _ = Complex.im
          (∫ x in Set.Ioi (0 : ℝ),
            (x : ℂ) ^ (n - 1) * Complex.exp (((-p : ℂ) + (q : ℂ) * Complex.I) * (x : ℂ)) ∂volume) := by
            exact integral_im hf
    _ = Complex.im
          (((Nat.factorial (n - 1) : ℂ) * (((p : ℂ) + (q : ℂ) * Complex.I) ^ n)) /
            (p ^ 2 + q ^ 2) ^ n) := by
            rw [integral_pow_pred_mul_exp_neg_mul_complex p q n hp hn]
    _ = (Nat.factorial (n - 1) : ℝ) * Complex.im (((p : ℂ) + (q : ℂ) * Complex.I) ^ n) /
          (p ^ 2 + q ^ 2) ^ n := by
            have hpow : ((((p ^ 2 + q ^ 2) ^ n : ℝ) : ℂ)) = (↑p ^ 2 + ↑q ^ 2) ^ n := by
              simp [Complex.ofReal_add, Complex.ofReal_pow]
            rw [← hpow]
            exact complex_scalar_im_div (Nat.factorial (n - 1)) ((p ^ 2 + q ^ 2) ^ n)
              (((p : ℂ) + (q : ℂ) * Complex.I) ^ n)
