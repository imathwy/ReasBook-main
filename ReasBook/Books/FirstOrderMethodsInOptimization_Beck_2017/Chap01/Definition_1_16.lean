import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
