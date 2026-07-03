import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_16 (from Chap01) -/
open Matrix
open scoped BigOperators RealInnerProductSpace

variable {n : ℕ}

/- Definition 1.16: `EuclideanSpace ℝ (Fin n)` is the canonical Lean model of `ℝ^n`, and its
inner product is the canonical Euclidean-space dot product from
`EuclideanSpace.inner_eq_star_dotProduct`. Over `ℝ`, conjugation is trivial, so this is exactly
the textbook formula `∑ i, x_i y_i`. -/
#check (EuclideanSpace.inner_eq_star_dotProduct :
  ∀ x y : EuclideanSpace ℝ (Fin n), ⟪x, y⟫ = dotProduct y x)

-- Proof sketch: rewrite the canonical Euclidean-space inner product as a dot product and unfold
-- `dotProduct` over `ℝ`.
/-- The standard inner product on `EuclideanSpace ℝ (Fin n)` is the textbook dot product. -/
theorem euclideanSpace_inner_eq_sum_mul (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, y⟫ = ∑ i, x i * y i := by
  simpa [dotProduct, mul_comm] using EuclideanSpace.inner_eq_star_dotProduct x y

/-! ### Proposition_1_16 (from Chap01) -/
variable {m n : ℕ}
variable (a b : ENNReal) [Fact (1 ≤ a)] [Fact (1 ≤ b)]
variable (A : Matrix (Fin m) (Fin n) ℝ)

/- Proposition 1.16 is recall-only: in the chapter owner setup from Definition 1.34, the induced
`(a,b)`-norm of a real matrix is exactly the operator norm of the continuous linear map attached
to `Matrix.toLpLin a b`. -/
#check (‖(A.toLpLin a b).toContinuousLinearMap‖ : ℝ)
