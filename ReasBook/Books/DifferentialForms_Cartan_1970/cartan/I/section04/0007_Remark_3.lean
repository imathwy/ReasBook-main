import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff
open scoped Topology
open Filter
open Polynomial

-- Semantic recall note: `lean_leansearch` is unavailable in this environment, so the canonical
-- owners were checked directly against mathlib's complex-analytic API and `expNegInvGlue`.

noncomputable section

/-- Helper for Remark 3: the real flat function from the textbook example. -/
abbrev flat_nonanalytic_formula : ℝ → ℝ :=
  fun x : ℝ ↦ if x = 0 then 0 else Real.exp (-1 / (x ^ 2))

/-- Helper for Remark 3: the recursive polynomial controlling iterated derivatives of the flat
function. -/
def flat_nonanalytic_formula_iteratedDerivPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      X ^ 2 *
        (C (2 : ℝ) * X * flat_nonanalytic_formula_iteratedDerivPolynomial n -
          derivative (flat_nonanalytic_formula_iteratedDerivPolynomial n))

/-- The explicit textbook flat-function formula agrees with mathlib's canonical smooth-transition
owner `x ↦ expNegInvGlue (x ^ 2)`. -/
theorem flat_nonanalytic_formula_eq_expNegInvGlue_sq :
    flat_nonanalytic_formula = fun x : ℝ ↦ expNegInvGlue (x ^ 2) := by
  funext x
  by_cases hx : x = 0
  · simp [flat_nonanalytic_formula, hx, expNegInvGlue]
  · have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    simp [flat_nonanalytic_formula, expNegInvGlue, hx, not_le_of_gt hx2, div_eq_mul_inv]

/- Remark 3 (1): a complex differentiable function is analytic at every point. -/
recall Differentiable.analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Differentiable ℂ f) (z : ℂ) :
  AnalyticAt ℂ f z

/- Remark 3 (2): a complex differentiable function of one complex variable is infinitely
differentiable. -/
recall Differentiable.contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Differentiable ℂ f) {n : WithTop ℕ∞} :
  ContDiff ℂ n f

/-- Helper for Remark 3: the function `x ↦ x * |x| / 2` has derivative `|x|`. -/
lemma primitive_abs_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y * |y| / 2) |x| x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · -- On the negative half-line, `|x| = -x`, so the product rule simplifies directly.
    simpa [abs_of_neg hx, two_mul, mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_id x).mul (hasDerivAt_abs_neg hx)).div_const (2 : ℝ)
  · -- At the origin, the slope is `|y| / 2`, and continuity of `abs` forces the limit to `0`.
    rw [hasDerivAt_iff_tendsto_slope]
    have hzero : Filter.Tendsto (fun y : ℝ ↦ |y| / 2) (𝓝[≠] (0 : ℝ)) (𝓝 (|0| / 2)) := by
      exact ((continuous_abs.continuousAt.div_const (2 : ℝ)).tendsto.mono_left inf_le_left)
    simpa using hzero.congr' (by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy0 : y ≠ 0 := by simpa [Set.mem_compl_iff] using hy
      -- Rewrite the punctured slope directly to the continuous model `|y| / 2`.
      simp [slope_def_field, hy0, div_eq_mul_inv, mul_assoc, mul_comm])
  · -- On the positive half-line, `|x| = x`, so the same product rule simplifies to `x`.
    simpa [abs_of_pos hx, two_mul, mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_id x).mul (hasDerivAt_abs_pos hx)).div_const (2 : ℝ)

/-- Remark 3 (3): there exists a differentiable real function whose derivative fails to be
differentiable at some point. -/
theorem exists_differentiable_with_nondifferentiable_deriv :
    ∃ f : ℝ → ℝ, Differentiable ℝ f ∧ ∃ x : ℝ, ¬ DifferentiableAt ℝ (deriv f) x := by
  refine ⟨fun x : ℝ ↦ x * |x| / 2, ?_, ?_⟩
  · -- The explicit primitive is differentiable everywhere because its derivative is known.
    intro x
    exact (primitive_abs_hasDerivAt x).differentiableAt
  · -- Its derivative is exactly `abs`, which is not differentiable at `0`.
    refine ⟨0, ?_⟩
    have hderiv : deriv (fun x : ℝ ↦ x * |x| / 2) = fun x : ℝ ↦ |x| := by
      funext x
      exact (primitive_abs_hasDerivAt x).deriv
    simpa [hderiv] using not_differentiableAt_abs_zero

/-- Remark 3 (4): the textbook flat function `x ↦ if x = 0 then 0 else exp (-1 / x^2)` is
infinitely differentiable on `ℝ`. -/
theorem contDiff_flat_nonanalytic_formula :
    ContDiff ℝ ∞ flat_nonanalytic_formula := by
  rw [flat_nonanalytic_formula_eq_expNegInvGlue_sq]
  simpa [Function.comp_apply] using
    (expNegInvGlue.contDiff.comp
      (contDiff_id.pow 2 : ContDiff ℝ ∞ (fun x : ℝ ↦ x ^ 2)))

/-- Helper for Remark 3: every reciprocal monomial times the flat factor tends to zero at the
origin. -/
lemma tendsto_X_pow_eval_inv_mul_flat_nonanalytic_formula_zero (n : ℕ) :
    Tendsto (fun x : ℝ ↦ (X ^ n).eval x⁻¹ * flat_nonanalytic_formula x) (𝓝 0) (𝓝 0) := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- Even powers reduce to the standard `expNegInvGlue` estimate after composing with `x ↦ x^2`.
    have hEven :
        Tendsto (fun x : ℝ ↦ ((x ^ 2)⁻¹) ^ m * expNegInvGlue (x ^ 2)) (𝓝 0) (𝓝 0) := by
      simpa [Polynomial.eval_pow] using
        (expNegInvGlue.tendsto_polynomial_inv_mul_zero (X ^ m)).comp
          (by simpa using ((continuous_id.pow 2).tendsto (0 : ℝ)))
    convert hEven using 1
    funext x
    -- Normalize the reciprocal monomial before matching the composed `expNegInvGlue` limit.
    rw [flat_nonanalytic_formula_eq_expNegInvGlue_sq, Polynomial.eval_pow, Polynomial.eval_X]
    by_cases hx : x = 0
    · simp [hx]
    · rw [show x⁻¹ ^ (m + m) = ((x ^ 2)⁻¹) ^ m by
          calc
            x⁻¹ ^ (m + m) = x⁻¹ ^ m * x⁻¹ ^ m := by rw [pow_add]
            _ = (x⁻¹ * x⁻¹) ^ m := by rw [← mul_pow]
            _ = ((x ^ 2)⁻¹) ^ m := by
              congr 1
              rw [pow_two, mul_inv_rev]]
  · -- Odd powers are `x` times the next even power, so the extra factor still preserves the limit.
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
    -- Peel off one factor of `x` so the odd case reduces to the even decay estimate.
    rw [flat_nonanalytic_formula_eq_expNegInvGlue_sq, Polynomial.eval_pow, Polynomial.eval_X,
      two_mul]
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

/-- Helper for Remark 3: polynomial reciprocal factors still tend to zero against the flat factor
at the origin. -/
lemma tendsto_polynomial_eval_inv_mul_flat_nonanalytic_formula_zero (p : ℝ[X]) :
    Tendsto (fun x : ℝ ↦ p.eval x⁻¹ * flat_nonanalytic_formula x) (𝓝 0) (𝓝 0) := by
  -- Decompose the polynomial into monomials and apply the monomial estimate termwise.
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    have hsum := hp.add hq
    simpa using hsum.congr' (by
      filter_upwards with x
      by_cases hx : x = 0
      · simp [flat_nonanalytic_formula, hx]
      · simp [flat_nonanalytic_formula, hx, add_mul])
  · intro n c
    simpa [Polynomial.eval_mul, Polynomial.eval_C, mul_assoc, mul_left_comm, mul_comm] using
      (tendsto_X_pow_eval_inv_mul_flat_nonanalytic_formula_zero n).const_mul c

/-- Helper for Remark 3: the derivative of a reciprocal-polynomial multiple of the flat factor is
again of the same form. -/
lemma hasDerivAt_polynomial_eval_inv_mul_flat_nonanalytic_formula (p : ℝ[X]) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ ↦ p.eval y⁻¹ * flat_nonanalytic_formula y)
      ((X ^ 2 * (C (2 : ℝ) * X * p - derivative p)).eval x⁻¹ * flat_nonanalytic_formula x)
      x := by
  by_cases hx : x = 0
  · -- At the origin, the slope is the same reciprocal-polynomial estimate with one extra `X`.
    subst hx
    rw [hasDerivAt_iff_tendsto_slope]
    have htarget :
        (X ^ 2 * (C (2 : ℝ) * X * p - derivative p)).eval (0 : ℝ)⁻¹ * flat_nonanalytic_formula 0 =
          0 := by
      simp [flat_nonanalytic_formula]
    rw [htarget]
    have hzero :
        Tendsto (fun y : ℝ ↦ (X * p).eval y⁻¹ * flat_nonanalytic_formula y) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      (tendsto_polynomial_eval_inv_mul_flat_nonanalytic_formula_zero (X * p)).mono_left inf_le_left
    refine hzero.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    -- Rewrite the slope into the reciprocal-polynomial factor handled by the zero-limit lemma.
    simp [slope_def_field, flat_nonanalytic_formula, Polynomial.eval_mul, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm]
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
      -- The product rule preserves the polynomial-times-flat shape.
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
        (fun y : ℝ ↦ p.eval y⁻¹ * flat_nonanalytic_formula y) =ᶠ[𝓝 x]
          fun y : ℝ ↦ p.eval y⁻¹ * Real.exp (-((y ^ 2)⁻¹)) := by
      have hAway : ({0} : Set ℝ)ᶜ ∈ 𝓝 x :=
        isOpen_compl_singleton.mem_nhds (by simpa [Set.mem_compl_iff] using hx)
      filter_upwards [hAway] with y hy
      have hy0 : y ≠ 0 := by simpa [Set.mem_compl_iff] using hy
      have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy0
      have hyexp : Real.exp (-1 / y ^ 2) = Real.exp (-((y ^ 2)⁻¹)) := by
        congr 1
        field_simp [hy2]
      rw [flat_nonanalytic_formula, if_neg hy0, hyexp]
    have hMain := hBase.congr_of_eventuallyEq hEq
    convert hMain using 2
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    have hxexp : Real.exp (-((x ^ 2)⁻¹)) = Real.exp (-1 / x ^ 2) := by
      congr 1
      field_simp [hx2]
    rw [flat_nonanalytic_formula, if_neg hx, hxexp]

/-- Helper for Remark 3: every iterated derivative of the flat function is a reciprocal-polynomial
multiple of the flat factor. -/
lemma iteratedDeriv_flat_nonanalytic_formula_eq_polynomial_eval_inv_mul (n : ℕ) :
    iteratedDeriv n flat_nonanalytic_formula =
      fun x : ℝ ↦ (flat_nonanalytic_formula_iteratedDerivPolynomial n).eval x⁻¹ *
        flat_nonanalytic_formula x := by
  induction n with
  | zero =>
    -- The zeroth iterated derivative is the function itself.
    funext x
    simp [flat_nonanalytic_formula_iteratedDerivPolynomial]
  | succ n ih =>
    -- Differentiate the induction formula and apply the polynomial recursion once more.
    rw [iteratedDeriv_succ, ih]
    funext x
    exact
      (hasDerivAt_polynomial_eval_inv_mul_flat_nonanalytic_formula
        (flat_nonanalytic_formula_iteratedDerivPolynomial n) x).deriv

/-- Remark 3 (5): every iterated derivative of the textbook flat function vanishes at `0`. -/
theorem iteratedDeriv_flat_nonanalytic_formula_zero (n : ℕ) :
    iteratedDeriv n flat_nonanalytic_formula 0 = 0 := by
  -- Route correction: the flat function is positive off `0`, so the proof uses the polynomial
  -- recursion behind mathlib's smooth `expNegInvGlue` argument instead of a false half-line claim.
  have h :=
    congrArg (fun f : ℝ → ℝ ↦ f 0)
      (iteratedDeriv_flat_nonanalytic_formula_eq_polynomial_eval_inv_mul n)
  simpa [flat_nonanalytic_formula] using h

/-- Helper for Remark 3: analyticity at `0` would force the flat function to have infinite
analytic order there. -/
lemma analyticOrderAt_flat_nonanalytic_formula_zero_eq_top_of_analytic
    (hf : AnalyticAt ℝ flat_nonanalytic_formula 0) :
    analyticOrderAt flat_nonanalytic_formula 0 = ⊤ := by
  -- All iterated derivatives vanish, so every natural order lies below the analytic order.
  refine ENat.eq_top_iff_forall_ge.2 ?_
  intro n
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
  intro i hi
  exact iteratedDeriv_flat_nonanalytic_formula_zero i

/-- Helper for Remark 3: the flat function is strictly positive at every positive point. -/
lemma flat_nonanalytic_formula_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < flat_nonanalytic_formula x := by
  -- On the positive half-line, the flat formula is the ordinary exponential expression.
  simpa [flat_nonanalytic_formula, hx.ne'] using Real.exp_pos (-1 / (x ^ 2))

/-- Remark 3 (6): the textbook flat function is not analytic at `0`. -/
theorem not_analyticAt_flat_nonanalytic_formula_zero :
    ¬ AnalyticAt ℝ flat_nonanalytic_formula 0 := by
  intro hf
  have htop : analyticOrderAt flat_nonanalytic_formula 0 = ⊤ :=
    analyticOrderAt_flat_nonanalytic_formula_zero_eq_top_of_analytic hf
  rw [analyticOrderAt_eq_top, Metric.eventually_nhds_iff] at htop
  obtain ⟨r, hr, hzero_ball⟩ := htop
  have hhalf_mem : dist (r / 2) 0 < r := by
    rw [Real.dist_eq]
    simpa [abs_of_pos (half_pos hr)] using half_lt_self hr
  have hzero : flat_nonanalytic_formula (r / 2) = 0 := hzero_ball hhalf_mem
  have hpos : 0 < flat_nonanalytic_formula (r / 2) :=
    flat_nonanalytic_formula_pos_of_pos (half_pos hr)
  exact hpos.ne' hzero
