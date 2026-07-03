import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_2 (from Chap01) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {n : ℕ} (v : Fin n → E)

/- Definition 1.2: a finite family of vectors in a real vector space is linearly independent
exactly when it is the canonical mathlib predicate `LinearIndependent ℝ v`. -/
#check (LinearIndependent ℝ v)

/- For a finite family, the textbook vanishing-linear-combination criterion is the canonical
mathlib theorem `Fintype.linearIndependent_iff`. -/
recall Fintype.linearIndependent_iff

end

/-! ### Proposition_1_2 (from Chap01) -/
noncomputable section

open scoped Matrix.Norms.L2Operator

section

variable {m n : ℕ}

private theorem transpose_mul_self_isHermitian (A : Matrix (Fin m) (Fin n) ℝ) :
    (A.transpose * A).IsHermitian := by
  simpa using Matrix.isHermitian_conjTranspose_mul_self A

private theorem zero_lt_fin_card (hn : 0 < n) : 0 < Fintype.card (Fin n) := by
  simpa using hn

-- Proof sketch: use the canonical `Matrix.Norms.L2Operator` norm, identify it with the operator
-- norm of `A.toEuclideanLin`, then apply the singular-value description
-- `T.singularValues 0 = √(eigenvalue₀(T†T))` together with
-- `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`.
/-- Proposition 1.2 (`source-facing`; `core/canonical` owner: `LinearMap.singularValues`;
`bridge/view`: `Matrix.Norms.L2Operator`): for a real matrix equipped with the Euclidean induced
operator norm, the norm equals its largest singular value. -/
theorem l2_induced_matrix_norm_eq_max_singular_value
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ = A.toEuclideanLin.singularValues 0 := sorry

/-- Companion bridge for Proposition 1.2 (`bridge/view`): the largest singular value of a real
matrix is the square root of the largest eigenvalue of the Gram matrix `Aᵀ A`. Since the
eigenvalues are listed in decreasing order, `⟨0, hn⟩` selects the largest one. -/
theorem max_singular_value_eq_sqrt_max_gram_eigenvalue
    (A : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n) :
    A.toEuclideanLin.singularValues 0 =
      Real.sqrt ((transpose_mul_self_isHermitian A).eigenvalues₀ ⟨0, zero_lt_fin_card hn⟩) := sorry

/-- Companion reformulation of Proposition 1.2 in Gram-matrix eigenvalue form. -/
theorem l2_induced_matrix_norm_eq_sqrt_max_gram_eigenvalue
    (A : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n) :
    ‖A‖ = Real.sqrt ((transpose_mul_self_isHermitian A).eigenvalues₀ ⟨0, zero_lt_fin_card hn⟩) := by
  exact (l2_induced_matrix_norm_eq_max_singular_value A).trans
    (max_singular_value_eq_sqrt_max_gram_eigenvalue A hn)

end
