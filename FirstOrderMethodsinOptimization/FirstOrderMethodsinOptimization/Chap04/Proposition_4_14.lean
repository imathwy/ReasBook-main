import FirstOrderMethodsinOptimization.Chap04.Theorem_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped BigOperators

noncomputable section

/- Proposition 4.14 is `source-facing` in the Chapter 4 conjugacy API. The `core/canonical`
owner abstraction is `conjugate_function` from Definition 4.1, and the relevant `bridge/view`
owner is `conjugate_function_separable_sum_eq_sum_conjugate_function` from Theorem 4.3. The only
primitive local data are the scalar and coordinatewise negative-entropy integrands; the scalar and
Euclidean dual arguments are derived from the owner dual API rather than stored as parallel local
definitions. -/

/-- The scalar negative-entropy integrand `t ↦ t log t` on `[0, ∞)`, extended by `∞` on the
negative ray. -/
def negative_entropy_scalar : ℝ → EReal :=
  fun t ↦ if 0 ≤ t then ((t * Real.log t : ℝ) : EReal) else ⊤

/-- The coordinatewise negative entropy on `ℝ^n`, modeled as `Fin n → ℝ`. -/
def negative_entropy_function {n : ℕ} : (Fin n → ℝ) → EReal :=
  fun x ↦ ∑ i, negative_entropy_scalar (x i)

-- Proof sketch: compute the supremum defining
-- `conjugate_function negative_entropy_scalar (LinearMap.toSpanSingleton ℝ ℝ s)`. On `[0, ∞)`,
-- maximize `t ↦ s * t - t * log t`; its derivative vanishes at `t = exp (s - 1)`, the second
-- derivative is negative, and the boundary value at `t = 0` is smaller, so the supremum equals
-- `exp (s - 1)`.
/-- Proposition 4.14 (1): the scalar conjugate of the negative-entropy integrand, expressed through
the Chapter 4 owner `conjugate_function`, is `s ↦ exp (s - 1)`. -/
theorem negative_entropy_scalar_conjugate_eq (s : ℝ) :
    conjugate_function negative_entropy_scalar (LinearMap.toSpanSingleton ℝ ℝ s) =
      ((Real.exp (s - 1) : ℝ) : EReal) := sorry

-- Proof sketch: view `negative_entropy_function` as the finite separable sum
-- `x ↦ ∑ i, negative_entropy_scalar (x i)` on `Fin n → ℝ` and apply
-- `conjugate_function_separable_sum_eq_sum_conjugate_function` to the coordinate dual family
-- `fun i ↦ LinearMap.toSpanSingleton ℝ ℝ (y i)`. The resulting product dual is exactly the
-- Euclidean pairing dual `dotProductEquiv ℝ (Fin n) y`.
/-- Proposition 4.14 (2): on `ℝ^n`, modeled as `Fin n → ℝ`, the conjugate of the coordinatewise
negative entropy, evaluated through the Euclidean pairing `dotProductEquiv`, is the sum of the
scalar conjugates on the coordinates. -/
theorem negative_entropy_function_conjugate_eq_sum_scalar_conjugates
    {n : ℕ} (y : Fin n → ℝ) :
    conjugate_function negative_entropy_function (dotProductEquiv ℝ (Fin n) y) =
      ∑ i, conjugate_function negative_entropy_scalar (LinearMap.toSpanSingleton ℝ ℝ (y i)) :=
  sorry

-- Proof sketch: combine `negative_entropy_function_conjugate_eq_sum_scalar_conjugates` with
-- `negative_entropy_scalar_conjugate_eq` coordinatewise and simplify the finite sum.
/-- Proposition 4.14 (3): the conjugate of the coordinatewise negative entropy on `ℝ^n` is the
sum of the exponentials `exp (y_i - 1)` over the coordinates. -/
theorem negative_entropy_function_conjugate_eq_sum_exp
    {n : ℕ} (y : Fin n → ℝ) :
    conjugate_function negative_entropy_function (dotProductEquiv ℝ (Fin n) y) =
      ∑ i, ((Real.exp (y i - 1) : ℝ) : EReal) := sorry

end
