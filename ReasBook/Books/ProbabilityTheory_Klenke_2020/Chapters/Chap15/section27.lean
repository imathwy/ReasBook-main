import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_27 (from Items/Chap15) -/
open scoped BigOperators ComplexOrder

noncomputable section

/-- Definition 15.27, in canonical additive-group form: a complex-valued function is positive
semidefinite if every finite difference-kernel matrix is positive semidefinite. Specializing to
`EuclideanSpace ℝ (Fin d)` recovers the textbook notion on `ℝ^d`. -/
def IsPositiveSemidefiniteFunction {G : Type*} [AddGroup G] (φ : G → ℂ) : Prop :=
  ∀ n (x : Fin n → G), (Matrix.of fun i j ↦ φ (x i - x j)).PosSemidef

-- Proof sketch: unfold `IsPositiveSemidefiniteFunction`, rewrite matrix positive semidefiniteness
-- with `Matrix.posSemidef_iff_dotProduct_mulVec`, and identify the resulting quadratic form with
-- the textbook double sum.
/-- A function is positive semidefinite exactly when all finite quadratic sums
`∑_{i,j} \overline{c_i} φ(x_i - x_j) c_j` are nonnegative in `ℂ`, equivalently are real and
nonnegative. -/
theorem isPositiveSemidefiniteFunction_iff_quadratic_sum_nonneg {G : Type*} [AddGroup G]
    {φ : G → ℂ} :
    IsPositiveSemidefiniteFunction φ ↔
      ∀ n (x : Fin n → G) (c : Fin n → ℂ),
        0 ≤ ∑ i, ∑ j, star (c i) * φ (x i - x j) * c j := sorry
