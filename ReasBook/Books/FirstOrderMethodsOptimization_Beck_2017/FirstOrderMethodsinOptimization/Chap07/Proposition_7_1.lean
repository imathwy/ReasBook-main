import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

noncomputable section

section

variable {n : ℕ}

/-- A real symmetric matrix is Hermitian. -/
-- Proof sketch: over `ℝ`, the conjugate transpose is the ordinary transpose, so `IsHermitian`
-- reduces to `IsSymm`.
theorem Matrix.IsSymm.isHermitian_of_real {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsSymm) :
    X.IsHermitian := by
  -- Over `ℝ`, Hermitian matrices are exactly symmetric matrices because conjugation is trivial.
  simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hX

/-- Proposition 7.1: every real symmetric matrix admits an orthogonal diagonalization whose
diagonal entries are the eigenvalues of the matrix. -/
-- Proof sketch: apply mathlib's Hermitian matrix spectral theorem to
-- `hX.isHermitian_of_real`, choose the orthogonal matrix
-- `hX.isHermitian_of_real.eigenvectorUnitary`, and rewrite the conjugate transpose over `ℝ` as the
-- ordinary transpose.
theorem symmetric_matrix_exists_orthogonal_diagonalization
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsSymm) :
    ∃ U : Matrix.orthogonalGroup (Fin n) ℝ,
      X = (U : Matrix (Fin n) (Fin n) ℝ) * diagonal (hX.isHermitian_of_real.eigenvalues) *
        (U : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
  let hH : X.IsHermitian := hX.isHermitian_of_real
  refine ⟨hH.eigenvectorUnitary, ?_⟩
  -- Route correction: use the Hermitian spectral theorem as the main skeleton, then rewrite the
  -- real conjugate-transpose expression into the orthogonal `U * diagonal * Uᵀ` form.
  simpa [hH, Unitary.conjStarAlgAut_apply, Matrix.conjTranspose_eq_transpose_of_trivial,
    Function.comp_apply, mul_assoc] using hH.spectral_theorem

end
