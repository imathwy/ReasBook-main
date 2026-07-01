import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold Matrix.Norms.Elementwise

section

set_option allowUnsafeReducibility true in
attribute [local reducible] Matrix

variable (m n : ℕ) in
/- Example 1.25: the space of real `m × n` matrices carries the canonical smooth manifold
structure on the model space `Matrix (Fin m) (Fin n) ℝ`. -/
#check
  (inferInstance : IsManifold 𝓘(ℝ, Matrix (Fin m) (Fin n) ℝ) ⊤
    (Matrix (Fin m) (Fin n) ℝ))

variable (m n : ℕ) in
/- The space of complex `m × n` matrices is likewise a smooth manifold over `ℝ` through its
underlying real vector-space structure. -/
#check
  (inferInstance : IsManifold 𝓘(ℝ, Matrix (Fin m) (Fin n) ℂ) ⊤
    (Matrix (Fin m) (Fin n) ℂ))

end

-- Proof sketch: apply `Module.finrank_matrix` to matrices over `ℝ` and simplify using
-- `Fintype.card (Fin m) = m`, `Fintype.card (Fin n) = n`, and `Module.finrank ℝ ℝ = 1`.
/-- Real `m × n` matrices have real dimension `mn`. -/
theorem finrank_real_rectangular_matrix (m n : ℕ) :
    Module.finrank ℝ (Matrix (Fin m) (Fin n) ℝ) = m * n := by
  simp [Module.finrank_matrix]

-- Proof sketch: apply `Module.finrank_matrix` to matrices over `ℂ`, rewrite
-- `Module.finrank ℝ ℂ = 2` using `Complex.finrank_real_complex`, and simplify the arithmetic.
/-- Complex `m × n` matrices have real dimension `2mn`. -/
theorem finrank_complex_rectangular_matrix_over_real (m n : ℕ) :
    Module.finrank ℝ (Matrix (Fin m) (Fin n) ℂ) = 2 * (m * n) := by
  rw [finrank_real_of_complex, Module.finrank_matrix]
  simp [Nat.mul_assoc, Nat.mul_comm]
