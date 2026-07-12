import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

/-- Example 2.5: for a strictly positive integer `N`, the real vector subspace of symmetric
`N × N` matrices is the canonical self-adjoint submodule of `Matrix (Fin N) (Fin N) ℝ`;
equivalently, membership is the library predicate `A.IsSymm`. -/
@[simp] theorem mem_selfAdjoint_submodule_iff_isSymm
    {N : ℕ+} {A : Matrix (Fin N) (Fin N) ℝ} :
    A ∈ selfAdjoint.submodule ℝ (Matrix (Fin N) (Fin N) ℝ) ↔ A.IsSymm := by
  change IsSelfAdjoint A ↔ A.IsSymm
  rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.IsSymm, Matrix.conjTranspose]
  constructor <;> intro h <;> simpa using h

/-- Example 2.5 in textbook coordinates: membership in the canonical self-adjoint submodule is the
condition `Aᵀ = A`. -/
theorem mem_selfAdjoint_submodule_iff
    {N : ℕ+} {A : Matrix (Fin N) (Fin N) ℝ} :
    A ∈ selfAdjoint.submodule ℝ (Matrix (Fin N) (Fin N) ℝ) ↔ Aᵀ = A := by
  rw [mem_selfAdjoint_submodule_iff_isSymm, Matrix.IsSymm]
