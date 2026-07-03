import Mathlib.Analysis.Matrix.Normed
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ToLin

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_1_28 (from Chap01/Sec01_04) -/
open Matrix
open scoped Manifold Matrix.Norms.Elementwise

-- Proof sketch: characterize full rank by the maximal possible image dimension `min m n`, then
-- transfer the openness statement to the corresponding set of linear maps of rank at least
-- `min m n` and use that `Matrix.toLin'` is a linear equivalence.
/-- The full-rank real `m × n` matrices form an open subset of the ambient matrix space. -/
theorem isOpen_fullRank_real_rectangular_matrices (m n : ℕ) :
    IsOpen {A : Matrix (Fin m) (Fin n) ℝ |
      Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) = min m n} := sorry

/-- The open subset of real `m × n` matrices having full rank `min m n`. -/
def fullRankRealRectangularMatrices (m n : ℕ) :
    TopologicalSpace.Opens (Matrix (Fin m) (Fin n) ℝ) where
  carrier := {A : Matrix (Fin m) (Fin n) ℝ |
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) = min m n}
  is_open' := isOpen_fullRank_real_rectangular_matrices m n

/-- The open subset of full-rank real `m × n` matrices inherits the ambient charted-space
structure from the matrix space. -/
noncomputable instance fullRankRealRectangularMatrices_chartedSpace (m n : ℕ) :
    ChartedSpace (Matrix (Fin m) (Fin n) ℝ) ↥(fullRankRealRectangularMatrices m n) :=
  inferInstance

variable (m n : ℕ) in
/- Example 1.28: the full-rank real `m × n` matrices form an open subset of the ambient matrix
space, so they inherit the canonical smooth manifold structure modeled on
`Matrix (Fin m) (Fin n) ℝ`; this covers the cases `m < n` and `n < m` discussed in the text. -/
#check (
  @inferInstance
    (@IsManifold ℝ _ (Matrix (Fin m) (Fin n) ℝ) _ _ (Matrix (Fin m) (Fin n) ℝ) _
      (modelWithCornersSelf ℝ (Matrix (Fin m) (Fin n) ℝ)) (⊤ : WithTop ℕ∞)
      ↥(fullRankRealRectangularMatrices m n) inferInstance
      (fullRankRealRectangularMatrices_chartedSpace m n)))

-- Proof sketch: specialize `finrank_matrix` to `Fin m` and `Fin n`, then simplify using
-- `Fintype.card (Fin m) = m`, `Fintype.card (Fin n) = n`, and `Module.finrank ℝ ℝ = 1`.
/-- The ambient real vector space of `m × n` matrices has dimension `mn`. -/
theorem finrank_real_rectangular_matrix_eq_mul (m n : ℕ) :
    Module.finrank ℝ (Matrix (Fin m) (Fin n) ℝ) = m * n := sorry
