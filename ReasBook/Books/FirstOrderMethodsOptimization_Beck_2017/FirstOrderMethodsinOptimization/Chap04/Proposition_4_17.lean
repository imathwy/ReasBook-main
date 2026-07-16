import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Proposition_4_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators

/- Proposition 4.17 is a `source-facing` conjugacy computation for the concrete log-sum-exp
function on `ℝ^n`. The chapter `core/canonical` owner declaration for the entropy-valued
right-hand side is already `negative_entropy_on_stdSimplex` from Proposition 4.16, built on the
Fenchel conjugate owner `conjugate_function` from Definition 4.1. This file therefore states the
conjugate formula directly using that named entropy object rather than restating its coordinate
definition inline. -/

section

variable {n : ℕ}

local notation "E" => Fin n → ℝ

/-- The log-sum-exp function `x ↦ log (∑ j, exp (x_j))` on `ℝ^n`, regarded as an
`EReal`-valued function so that its Fenchel conjugate is expressed by `conjugate_function`. -/
def log_sum_exp_function : E → EReal :=
  fun x ↦ ((Real.log (∑ j : Fin n, Real.exp (x j)) : ℝ) : EReal)

-- Proof sketch: unfold `log_sum_exp_function`; the statement is exactly its defining coordinate
-- formula cast from `ℝ` to `EReal`.
/-- Evaluating `log_sum_exp_function` at `x` gives `log (∑ j, exp (x_j))`, viewed in `EReal`. -/
theorem log_sum_exp_function_apply (x : E) :
    log_sum_exp_function x = ((Real.log (∑ j : Fin n, Real.exp (x j)) : ℝ) : EReal) :=
  rfl

variable [Nonempty (Fin n)]

-- Proof sketch: if `y ∉ stdSimplex ℝ (Fin n)`, either `∑ i, y i ≠ 1` or some coordinate is
-- negative; in each case a one-parameter family of test points makes the affine term minus
-- `log_sum_exp_function` diverge to `∞`. If `y ∈ stdSimplex ℝ (Fin n)`, rewrite the objective
-- using the softmax probabilities `p_i(x) = exp (x_i) / ∑ j, exp (x_j)`, reduce the supremum to
-- `sup_{p ∈ Δ_n} ∑ i, y_i log p_i`, and maximize it at `p = y` via Gibbs' inequality, using
-- `Real.log 0 = 0` for the convention `0 log 0 = 0`.
/-- Proposition 4.17: the Fenchel conjugate of the log-sum-exp function on `ℝ^n`, evaluated via
the Euclidean pairing `dotProductEquiv`, is the simplex-constrained negative entropy
`negative_entropy_on_stdSimplex n`. Equivalently, this is the entropy expression
`∑ i, y_i log y_i` on the standard simplex `Δ_n = stdSimplex ℝ (Fin n)` and `∞` outside the
simplex. -/
theorem log_sum_exp_function_conjugate_eq
    (y : E) :
    conjugate_function log_sum_exp_function (dotProductEquiv ℝ (Fin n) y) =
      negative_entropy_on_stdSimplex n y := sorry

end
