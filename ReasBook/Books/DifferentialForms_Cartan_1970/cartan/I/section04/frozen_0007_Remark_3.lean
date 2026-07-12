import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology ContDiff
open Filter
open Polynomial

/-- The square pullback of mathlib's owner `expNegInvGlue` matches the textbook flat function:
it is `0` at the origin and `exp (-1 / x^2)` away from `0`. -/
lemma expNegInvGlue_sq_apply (x : ℝ) :
    expNegInvGlue (x ^ 2) = if x = 0 then 0 else Real.exp (-1 / x ^ 2) := by
  by_cases hx : x = 0
  · simp [hx]
  · have hxsq : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    simp [expNegInvGlue, hx, not_le_of_gt hxsq, div_eq_mul_inv]

/-- Helper for Cartan section04 frozen_0007_Remark_3: the textbook flat function written in its
piecewise real-variable form. -/
noncomputable abbrev flatNonanalyticFormula : ℝ → ℝ :=
  fun x : ℝ ↦ if x = 0 then 0 else Real.exp (-1 / (x ^ 2))

/-- Helper for Cartan section04 frozen_0007_Remark_3: the recursive polynomial controlling the
iterated derivatives of the flat function. -/
noncomputable def flatNonanalyticFormulaIteratedDerivPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      X ^ 2 *
        (C (2 : ℝ) * X * flatNonanalyticFormulaIteratedDerivPolynomial n -
          derivative (flatNonanalyticFormulaIteratedDerivPolynomial n))

/-- Helper for Cartan section04 frozen_0007_Remark_3: the textbook formula agrees with the owner
expression `x ↦ expNegInvGlue (x ^ 2)`. -/
lemma flatNonanalyticFormula_eq_expNegInvGlueSq :
    flatNonanalyticFormula = fun x : ℝ ↦ expNegInvGlue (x ^ 2) := by
  funext x
  -- Rewrite once so the later derivative arguments can stay in the textbook formulation.
  simpa [flatNonanalyticFormula] using (expNegInvGlue_sq_apply x).symm

/-- Helper for Cartan section04 frozen_0007_Remark_3: the function `x ↦ x * |x| / 2` has
derivative `|x|`. -/
lemma primitiveAbs_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y * |y| / 2) |x| x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · -- On the negative half-line, `|x| = -x`, so the product rule simplifies directly.
    simpa [abs_of_neg hx, two_mul, mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_id x).mul (hasDerivAt_abs_neg hx)).div_const (2 : ℝ)
  · -- At the origin, the slope collapses to `|y| / 2`, and continuity of `abs` gives the limit.
    rw [hasDerivAt_iff_tendsto_slope]
    have hzero : Tendsto (fun y : ℝ ↦ |y| / 2) (𝓝[≠] (0 : ℝ)) (𝓝 (|0| / 2)) := by
      exact ((continuous_abs.continuousAt.div_const (2 : ℝ)).tendsto.mono_left inf_le_left)
    simpa using hzero.congr' (by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy0 : y ≠ 0 := by simpa [Set.mem_compl_iff] using hy
      -- Rewrite the punctured slope to the continuous comparison function `|y| / 2`.
      simp [slope_def_field, hy0, div_eq_mul_inv, mul_assoc, mul_comm])
  · -- On the positive half-line, `|x| = x`, so the same product rule yields the target value.
    simpa [abs_of_pos hx, two_mul, mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_id x).mul (hasDerivAt_abs_pos hx)).div_const (2 : ℝ)

/-- Helper for Cartan section04 frozen_0007_Remark_3: every reciprocal monomial times the flat
factor still tends to `0` at the origin. -/
lemma tendstoXPowEvalInvMulFlatNonanalyticFormulaZero (n : ℕ) :
    Tendsto (fun x : ℝ ↦ (X ^ n).eval x⁻¹ * flatNonanalyticFormula x) (𝓝 0) (𝓝 0) := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- Even powers reduce to the standard owner estimate after composing with `x ↦ x ^ 2`.
    have hEven :
        Tendsto (fun x : ℝ ↦ ((x ^ 2)⁻¹) ^ m * expNegInvGlue (x ^ 2)) (𝓝 0) (𝓝 0) := by
      simpa [Polynomial.eval_pow] using
        (expNegInvGlue.tendsto_polynomial_inv_mul_zero (X ^ m)).comp
          (by simpa using ((continuous_id.pow 2).tendsto (0 : ℝ)))
    convert hEven using 1
    funext x
    -- Normalize the reciprocal power before matching the owner-side limit.
    rw [flatNonanalyticFormula_eq_expNegInvGlueSq, Polynomial.eval_pow, Polynomial.eval_X]
    by_cases hx : x = 0
    · simp [hx]
    · rw [show x⁻¹ ^ (m + m) = ((x ^ 2)⁻¹) ^ m by
          calc
            x⁻¹ ^ (m + m) = x⁻¹ ^ m * x⁻¹ ^ m := by rw [pow_add]
            _ = (x⁻¹ * x⁻¹) ^ m := by rw [← mul_pow]
            _ = ((x ^ 2)⁻¹) ^ m := by
              congr 1
              rw [pow_two, mul_inv_rev]]
  · -- Odd powers are one extra factor of `x`, which still preserves the same zero limit.
    have hEven :
        Tendsto (fun x : ℝ ↦ ((x ^ 2)⁻¹) ^ (m + 1) * expNegInvGlue (x ^ 2)) (𝓝 0) (𝓝 0) := by
      simpa [Polynomial.eval_pow] using
        (expNegInvGlue.tendsto_polynomial_inv_mul_zero (X ^ (m + 1))).comp
          (by simpa using ((continuous_id.pow 2).tendsto (0 : ℝ)))
    have hOdd :
        Tendsto
          (fun x : ℝ ↦ x * (((x ^ 2)⁻¹) ^ (m + 1) * expNegInvGlue (x ^ 2)))
          (𝓝 0) (𝓝 0) := by
      have hid : Tendsto (fun x : ℝ ↦ x) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_id.tendsto (0 : ℝ))
      simpa using hid.mul hEven
    convert hOdd using 1
    funext x
    -- Peel off one copy of `x` so the remaining power is even.
    rw [flatNonanalyticFormula_eq_expNegInvGlueSq, Polynomial.eval_pow, Polynomial.eval_X, two_mul]
    by_cases hx : x = 0
    · simp [hx]
    · have hOddPow : x⁻¹ ^ (m + m + 1) = x * ((x ^ 2)⁻¹) ^ (m + 1) := by
        have hEvenPow : x⁻¹ ^ (m + m) = ((x ^ 2)⁻¹) ^ m := by
          calc
            x⁻¹ ^ (m + m) = x⁻¹ ^ m * x⁻¹ ^ m := by rw [pow_add]
            _ = (x⁻¹ * x⁻¹) ^ m := by rw [← mul_pow]
            _ = ((x ^ 2)⁻¹) ^ m := by
              congr 1
              rw [pow_two, mul_inv_rev]
        have hxinv : x⁻¹ = x * (x ^ 2)⁻¹ := by
          rw [pow_two, mul_inv_rev]
          field_simp [hx]
        calc
          x⁻¹ ^ (m + m + 1) = x⁻¹ ^ (m + m) * x⁻¹ := by rw [pow_add, pow_one]
          _ = ((x ^ 2)⁻¹) ^ m * x⁻¹ := by rw [hEvenPow]
          _ = ((x ^ 2)⁻¹) ^ m * (x * (x ^ 2)⁻¹) := by rw [hxinv]
          _ = x * (((x ^ 2)⁻¹) ^ m * (x ^ 2)⁻¹) := by ring
          _ = x * ((x ^ 2)⁻¹) ^ (m + 1) := by simp [pow_succ]
      rw [hOddPow]
      simp [mul_assoc]

/-- Helper for Cartan section04 frozen_0007_Remark_3: arbitrary reciprocal-polynomial multiples
of the flat factor still tend to `0` at the origin. -/
lemma tendstoPolynomialEvalInvMulFlatNonanalyticFormulaZero (p : ℝ[X]) :
    Tendsto (fun x : ℝ ↦ p.eval x⁻¹ * flatNonanalyticFormula x) (𝓝 0) (𝓝 0) := by
  -- Decompose the polynomial into monomials and apply the monomial estimate termwise.
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    have hsum := hp.add hq
    simpa using hsum.congr' (by
      filter_upwards with x
      by_cases hx : x = 0
      · simp [flatNonanalyticFormula, hx]
      · simp [flatNonanalyticFormula, hx, add_mul])
  · intro n c
    simpa [Polynomial.eval_mul, Polynomial.eval_C, mul_assoc, mul_left_comm, mul_comm] using
      (tendstoXPowEvalInvMulFlatNonanalyticFormulaZero n).const_mul c

/-- Helper for Cartan section04 frozen_0007_Remark_3: differentiating a reciprocal-polynomial
multiple of the flat factor stays inside the same family. -/
lemma hasDerivAtPolynomialEvalInvMulFlatNonanalyticFormula (p : ℝ[X]) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ ↦ p.eval y⁻¹ * flatNonanalyticFormula y)
      ((X ^ 2 * (C (2 : ℝ) * X * p - derivative p)).eval x⁻¹ * flatNonanalyticFormula x)
      x := by
  by_cases hx : x = 0
  · -- At the origin, rewrite the slope so the zero-limit lemma closes the derivative claim.
    subst hx
    rw [hasDerivAt_iff_tendsto_slope]
    have htarget :
        (X ^ 2 * (C (2 : ℝ) * X * p - derivative p)).eval (0 : ℝ)⁻¹ * flatNonanalyticFormula 0 =
          0 := by
      simp [flatNonanalyticFormula]
    rw [htarget]
    have hzero :
        Tendsto (fun y : ℝ ↦ (X * p).eval y⁻¹ * flatNonanalyticFormula y) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      (tendstoPolynomialEvalInvMulFlatNonanalyticFormulaZero (X * p)).mono_left inf_le_left
    refine hzero.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    -- The punctured slope is exactly one extra factor of `y⁻¹`.
    simp [slope_def_field, flatNonanalyticFormula, Polynomial.eval_mul, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]
  · -- Away from the origin, differentiate the explicit exponential formula and simplify.
    have hPoly :
        HasDerivAt (fun y : ℝ ↦ p.eval y⁻¹)
          (-(x ^ 2)⁻¹ * (derivative p).eval x⁻¹) x := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (p.hasDerivAt x⁻¹).comp x (hasDerivAt_inv hx)
    have hExp :
        HasDerivAt
          (fun y : ℝ ↦ Real.exp (-((y ^ 2)⁻¹)))
          ((2 / x ^ 3) * Real.exp (-((x ^ 2)⁻¹)))
          x := by
      have hInnerBase :
          HasDerivAt (fun y : ℝ ↦ -((y ^ 2)⁻¹))
            (-(-((2 * x) / (x ^ 2) ^ 2)))
            x := by
        simpa [pow_two, two_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          (((hasDerivAt_id x).pow 2).inv (pow_ne_zero 2 hx)).neg
      have hInner : HasDerivAt (fun y : ℝ ↦ -((y ^ 2)⁻¹)) (2 / x ^ 3) x := by
        have hcalc : -(-((2 * x) / (x ^ 2) ^ 2)) = 2 / x ^ 3 := by
          field_simp [hx, pow_ne_zero 2 hx]
        simpa [hcalc] using hInnerBase
      simpa [mul_comm] using hInner.exp
    have hBase' :
        HasDerivAt
          (fun y : ℝ ↦ p.eval y⁻¹ * Real.exp (-((y ^ 2)⁻¹)))
          (((x ^ 2)⁻¹ * (2 * x⁻¹ * p.eval x⁻¹ - (derivative p).eval x⁻¹)) *
            Real.exp (-((x ^ 2)⁻¹)))
          x := by
      -- The product rule preserves the reciprocal-polynomial-times-flat shape.
      convert hPoly.mul hExp using 1
      simp [pow_succ, div_eq_mul_inv, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
      ring
    have hBase :
        HasDerivAt
          (fun y : ℝ ↦ p.eval y⁻¹ * Real.exp (-((y ^ 2)⁻¹)))
          ((X ^ 2 * (C (2 : ℝ) * X * p - derivative p)).eval x⁻¹ *
            Real.exp (-((x ^ 2)⁻¹)))
          x := by
      have hsqinv : (x⁻¹) ^ 2 = (x ^ 2)⁻¹ := by
        rw [pow_two, pow_two, mul_inv_rev]
      convert hBase' using 2
      -- Evaluate the recursive polynomial explicitly at `x⁻¹`.
      rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
      simp [hsqinv]
    have hEq :
        (fun y : ℝ ↦ p.eval y⁻¹ * flatNonanalyticFormula y) =ᶠ[𝓝 x]
          fun y : ℝ ↦ p.eval y⁻¹ * Real.exp (-((y ^ 2)⁻¹)) := by
      have hAway : ({0} : Set ℝ)ᶜ ∈ 𝓝 x :=
        isOpen_compl_singleton.mem_nhds (by simpa [Set.mem_compl_iff] using hx)
      filter_upwards [hAway] with y hy
      have hy0 : y ≠ 0 := by simpa [Set.mem_compl_iff] using hy
      have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy0
      have hyexp : Real.exp (-1 / y ^ 2) = Real.exp (-((y ^ 2)⁻¹)) := by
        congr 1
        field_simp [hy2]
      rw [flatNonanalyticFormula, if_neg hy0, hyexp]
    have hMain := hBase.congr_of_eventuallyEq hEq
    convert hMain using 2
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    have hxexp : Real.exp (-((x ^ 2)⁻¹)) = Real.exp (-1 / x ^ 2) := by
      congr 1
      field_simp [hx2]
    rw [flatNonanalyticFormula, if_neg hx, hxexp]

/-- Helper for Cartan section04 frozen_0007_Remark_3: every iterated derivative of the flat
function is again a reciprocal-polynomial multiple of the same flat factor. -/
lemma iteratedDerivFlatNonanalyticFormula_eq_polynomialEvalInvMul (n : ℕ) :
    iteratedDeriv n flatNonanalyticFormula =
      fun x : ℝ ↦ (flatNonanalyticFormulaIteratedDerivPolynomial n).eval x⁻¹ *
        flatNonanalyticFormula x := by
  induction n with
  | zero =>
    -- The zeroth iterated derivative is the function itself.
    funext x
    simp [flatNonanalyticFormulaIteratedDerivPolynomial]
  | succ n ih =>
    -- Differentiate the induction formula and apply the recursive polynomial formula once.
    rw [iteratedDeriv_succ, ih]
    funext x
    exact
      (hasDerivAtPolynomialEvalInvMulFlatNonanalyticFormula
        (flatNonanalyticFormulaIteratedDerivPolynomial n) x).deriv

/-- Helper for Cartan section04 frozen_0007_Remark_3: every iterated derivative of the textbook
flat function vanishes at the origin. -/
lemma iteratedDerivFlatNonanalyticFormula_zero (n : ℕ) :
    iteratedDeriv n flatNonanalyticFormula 0 = 0 := by
  -- Evaluate the explicit reciprocal-polynomial formula at `0`.
  have h :=
    congrArg (fun f : ℝ → ℝ ↦ f 0)
      (iteratedDerivFlatNonanalyticFormula_eq_polynomialEvalInvMul n)
  simpa [flatNonanalyticFormula] using h

/-- The textbook flat function `x ↦ expNegInvGlue (x ^ 2)` is infinitely differentiable on `ℝ`. -/
-- Proof sketch: compose mathlib's owner theorem `expNegInvGlue.contDiff` with the polynomial map
-- `x ↦ x ^ 2`.
lemma expNegInvGlue_sq_contDiff : ContDiff ℝ ∞ (fun x : ℝ ↦ expNegInvGlue (x ^ 2)) := by
  -- Compose the canonical smooth-transition theorem with the polynomial map `x ↦ x ^ 2`.
  have hexp : ContDiff ℝ ∞ expNegInvGlue := by
    simpa using (expNegInvGlue.contDiff (n := (⊤ : ℕ∞)))
  have hsq : ContDiff ℝ ∞ (fun x : ℝ ↦ x ^ 2) := by
    simpa using (contDiff_id.pow 2 : ContDiff ℝ ∞ (fun x : ℝ ↦ x ^ 2))
  simpa [Function.comp_apply] using hexp.comp hsq

/-- Every iterated derivative of the textbook flat function vanishes at the origin. -/
-- Proof sketch: work from the owner-based identity `expNegInvGlue (x ^ 2)`,
-- show by induction that
-- each iterated derivative is a polynomial in `x⁻¹` times the same rapidly decaying exponential,
-- and then take the limit at `0`.
lemma expNegInvGlue_sq_iteratedDeriv_zero (n : ℕ) :
    iteratedDeriv n (fun x : ℝ ↦ expNegInvGlue (x ^ 2)) 0 = 0 := by
  -- Rewrite to the textbook piecewise formula and reuse the recursive derivative computation.
  rw [← flatNonanalyticFormula_eq_expNegInvGlueSq]
  exact iteratedDerivFlatNonanalyticFormula_zero n

/-- There exists a real-valued function that is differentiable on `ℝ` but whose derivative is not
differentiable at some point. -/
-- Proof sketch: start from a continuous function that fails to be differentiable at some point and
-- integrate it on intervals `0..x`; the fundamental theorem of calculus gives a differentiable
-- primitive whose derivative recovers the original continuous counterexample.
theorem exists_differentiable_with_no_second_derivative :
    ∃ f : ℝ → ℝ, Differentiable ℝ f ∧ ∃ x : ℝ, ¬ DifferentiableAt ℝ (deriv f) x := by
  refine ⟨fun x : ℝ ↦ x * |x| / 2, ?_, ?_⟩
  · -- The explicit primitive is differentiable everywhere because its derivative is known.
    intro x
    exact (primitiveAbs_hasDerivAt x).differentiableAt
  · -- Its derivative is `abs`, and `abs` is not differentiable at the origin.
    refine ⟨0, ?_⟩
    have hderiv : deriv (fun x : ℝ ↦ x * |x| / 2) = fun x : ℝ ↦ |x| := by
      funext x
      exact (primitiveAbs_hasDerivAt x).deriv
    simpa [hderiv] using not_differentiableAt_abs_zero

/-- Cartan section04 frozen_0007_Remark_3: the function that is `0` at `0` and `exp (-1 / x^2)`
for `x ≠ 0`, equivalently `x ↦ expNegInvGlue (x ^ 2)`, is smooth on `ℝ` but is not analytic at
the origin. -/
lemma expNegInvGlue_sq_not_analyticAt_zero :
    ¬ AnalyticAt ℝ (fun x : ℝ ↦ expNegInvGlue (x ^ 2)) 0 := by
  intro hanalytic
  have htop : analyticOrderAt (fun x : ℝ ↦ expNegInvGlue (x ^ 2)) 0 = ⊤ := by
    apply le_antisymm le_top
    refine ENat.forall_natCast_le_iff_le.mp fun n _ ↦ ?_
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hanalytic]
    intro i hi
    exact expNegInvGlue_sq_iteratedDeriv_zero i
  rcases Metric.eventually_nhds_iff.mp (analyticOrderAt_eq_top.mp htop) with ⟨r, hr, hzero⟩
  have hhalf : r / 2 < r := by linarith
  have habs_half : |r| / 2 < r := by
    simpa [abs_of_pos hr] using hhalf
  have hvalue : expNegInvGlue ((r / 2) ^ 2) = 0 := by
    apply hzero
    simpa [Real.dist_eq, sub_zero] using habs_half
  have hpos : 0 < expNegInvGlue ((r / 2) ^ 2) :=
    expNegInvGlue.pos_of_pos (sq_pos_of_pos (half_pos hr))
  exact hpos.ne' hvalue

/-- Helper for Cartan section04 frozen_0007_Remark_3: complex differentiability implies
analyticity and smoothness, while over `ℝ` there are differentiable functions with no second
derivative and smooth functions that are not analytic. -/
theorem realAndComplexDifferentiabilityContrast :
    (∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      {f : ℂ → E} {z : ℂ}, Differentiable ℂ f → AnalyticAt ℂ f z) ∧
      (∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
        {f : ℂ → E}, Differentiable ℂ f → ContDiff ℂ ∞ f) ∧
      (∃ f : ℝ → ℝ, Differentiable ℝ f ∧ ∃ x : ℝ, ¬ DifferentiableAt ℝ (deriv f) x) ∧
      (ContDiff ℝ ∞ (fun x : ℝ ↦ expNegInvGlue (x ^ 2)) ∧
        ¬ AnalyticAt ℝ (fun x : ℝ ↦ expNegInvGlue (x ^ 2)) 0) := by
  refine ⟨?_, ?_⟩
  · intro E _ _ _ f z hf
    exact hf.analyticAt z
  · refine ⟨?_, ?_⟩
    · intro E _ _ _ f hf
      simpa using (hf.contDiff : ContDiff ℂ ∞ f)
    · refine ⟨exists_differentiable_with_no_second_derivative, ?_⟩
      exact ⟨expNegInvGlue_sq_contDiff, expNegInvGlue_sq_not_analyticAt_zero⟩
