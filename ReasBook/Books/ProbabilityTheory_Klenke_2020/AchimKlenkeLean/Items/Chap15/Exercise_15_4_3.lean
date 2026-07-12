import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/-- The candidate function `t ↦ exp (-|t|^α)` appearing in Exercise 15.4.3. -/
noncomputable def phi_alpha (α : ℝ) : ℝ → ℂ :=
  fun t ↦ Complex.exp (-(Real.rpow |t| α))

-- Proof sketch: evaluate the defining formula for `phi_alpha` at `t = 0`, use `|0| = 0`,
-- `Real.zero_rpow` for positive exponent, and `Complex.exp_zero`.
/-- The function `phi_alpha` is normalized at the origin when `α` is positive. -/
theorem phi_alpha_zero (α : ℝ) (hα : 0 < α) :
    phi_alpha α 0 = 1 := sorry

-- Proof sketch: assume `charFun μ = phi_alpha α`, use the second-order expansion of
-- characteristic functions with finite second moment to identify the quadratic coefficient with the
-- variance, then compare with the flatter-than-quadratic behavior of `exp (-|t|^α)` at `0` when
-- `α > 2` to deduce zero variance and hence degeneracy, contradicting the nontrivial expansion.
/-- Exercise 15.4.3: for `α > 2`, the function `φ_α(t) = exp (-|t|^α)` is not the characteristic
function of a probability measure on `ℝ`. -/
theorem not_exists_probabilityMeasure_charFun_eq_phi_alpha (α : ℝ) (hα : 2 < α) :
    ¬ ∃ μ : ProbabilityMeasure ℝ, charFun (μ : Measure ℝ) = phi_alpha α := sorry
