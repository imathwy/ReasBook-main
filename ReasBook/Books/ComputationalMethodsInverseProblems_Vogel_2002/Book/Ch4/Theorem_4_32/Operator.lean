module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

noncomputable section

open scoped Matrix

namespace LinearGaussian

universe u v

section

variable {m : Type u} {n : Type v}
variable [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n]

/-- The precision-form Gauss-Markov operator matrix `(Kᵀ * C_N⁻¹ * K)⁻¹ * Kᵀ * C_N⁻¹`. -/
def gaussMarkovOperator (K : Matrix m n ℝ) (C_N : Matrix m m ℝ) : Matrix n m ℝ :=
  (Kᵀ * C_N⁻¹ * K)⁻¹ * Kᵀ * C_N⁻¹

/-- The defining formula for `LinearGaussian.gaussMarkovOperator`. -/
theorem gaussMarkovOperator_def (K : Matrix m n ℝ) (C_N : Matrix m m ℝ) :
    gaussMarkovOperator K C_N = (Kᵀ * C_N⁻¹ * K)⁻¹ * Kᵀ * C_N⁻¹ := by
  rfl

end

end LinearGaussian
