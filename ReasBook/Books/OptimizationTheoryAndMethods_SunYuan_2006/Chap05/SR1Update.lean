import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- The SR1 residual vector `y - B.mulVec s` used in the Chapter 5 SR1 formulas. -/
def sr1Residual (B : MatrixN) (s y : Point) : Point :=
  y - Matrix.toEuclideanLin B s

/-- The Chapter 5 symmetric rank-one inverse-Hessian update
`H + (dotProduct (sr1Residual H y s) y)⁻¹ •
  Matrix.vecMulVec (sr1Residual H y s) (sr1Residual H y s)`. -/
def sr1Update (H : MatrixN) (s y : Point) : MatrixN :=
  H + (dotProduct (sr1Residual H y s) y)⁻¹ •
    Matrix.vecMulVec (sr1Residual H y s) (sr1Residual H y s)

end
