import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_14 (from Chap01) -/
universe u

open scoped RealInnerProductSpace

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 1.14 is recall-only: mathlib's public `EuclideanSpace ℝ ι` is the concrete
coordinate model used later for `ℝ^n`, not the owner abstraction for an abstract Euclidean space.
For an abstract Euclidean space, the primitive owner abstractions are the real inner product
structure and the finite-dimensionality predicate below. -/

/- Definition 1.14 (1): a Euclidean space carries the canonical real inner product structure
`InnerProductSpace ℝ E`. -/
#check InnerProductSpace ℝ E

/- Definition 1.14 (2): a Euclidean space is finite-dimensional, encoded by the canonical
typeclass `FiniteDimensional ℝ E`. -/
#check FiniteDimensional ℝ E

/- Definition 1.14 (3): the Euclidean norm is derived from the ambient real inner product space,
canonically identified with `√⟪x, x⟫_ℝ` by `norm_eq_sqrt_real_inner`. -/
#check norm_eq_sqrt_real_inner

end

/-! ### Proposition_1_14 (from Chap01) -/
/- Proposition 1.14: the transpose operation on matrices is involutive, so transposing twice
returns the original matrix. -/
recall Matrix.transpose_transpose
