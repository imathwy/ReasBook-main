import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MatrixGroups
open scoped Matrix.Norms.Elementwise
open Matrix

-- Domain sampling in the matrix-calculus owner layer:
-- `Matrix.derivative_det_one_add_X_smul`, `Matrix.det_one_add_smul`, `Matrix.det`, and `GL`.
-- The theorems below keep the textbook source-facing statements, but use those owners directly.

/-- Helper for Problem 7-4: the determinant of `1 + t • A` has derivative `trace A` at `t = 0`. -/
lemma detOneAddSmul_hasDerivAtZero (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ ↦ (1 + t • A).det) A.trace 0 := by
  sorry

/-- Helper for Problem 7-4: the determinant map on real square matrices is differentiable at every
matrix. -/
lemma matrixDet_differentiableAt (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) :
    DifferentiableAt ℝ Matrix.det X := by
  sorry

/-- Helper for Problem 7-4: along the affine line `t ↦ X + t • B` through an invertible matrix,
the determinant has derivative `det X * trace (X⁻¹ * B)` at `t = 0`. -/
lemma detAlongLineAtInvertible_hasDerivAt (n : ℕ) (X : GL (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ Matrix.det ((X : Matrix (Fin n) (Fin n) ℝ) + t • B))
      ((X : Matrix (Fin n) (Fin n) ℝ).det *
        ((((X⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) * B).trace))
      0 := by
  sorry

/-- Problem 7-4 (1): for any real `n × n` matrix `A`, the derivative at `t = 0` of
`det (I + tA)` is `tr A`. -/
theorem det_deriv_one_add_smul_eq_trace (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    deriv (fun t : ℝ ↦ (1 + t • A).det) 0 = A.trace := by
  sorry

/-- Problem 7-4 (2): under the canonical identification of `T_X GL(n, ℝ)` with the ambient
matrix space, the differential of the determinant at `X` applied to `B` is
`det(X) * tr(X⁻¹ B)`. -/
theorem generalLinear_det_fderiv_apply (n : ℕ) (X : GL (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    fderiv ℝ Matrix.det (X : Matrix (Fin n) (Fin n) ℝ) B =
      (X : Matrix (Fin n) (Fin n) ℝ).det *
        ((((X⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) * B).trace) := by
  sorry
