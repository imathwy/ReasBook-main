

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_33 (from Chap01) -/
open scoped BigOperators Matrix Matrix.Norms.Frobenius

noncomputable section

open Matrix InnerProductSpace

variable {m n : ℕ}

/- Definition 1.33: the Euclidean norm on `ℝ^{m × n}` coming from the matrix dot product is the
canonical Frobenius norm, implemented by `Matrix.frobeniusNormedAddCommGroup`. -/
#check (Matrix.frobeniusNormedAddCommGroup : NormedAddCommGroup (Matrix (Fin m) (Fin n) ℝ))

private def matrixToLp (A : Matrix (Fin m) (Fin n) ℝ) :
    WithLp 2 (Fin m → WithLp 2 (Fin n → ℝ)) :=
  WithLp.toLp 2 fun i ↦ WithLp.toLp 2 fun j ↦ A i j

/-- The Frobenius Euclidean structure on real matrices, obtained from the canonical `ℓ²`
identification with nested `WithLp 2` spaces. -/
@[instance_reducible] def Matrix.frobeniusInnerProductSpace :
    InnerProductSpace ℝ (Matrix (Fin m) (Fin n) ℝ) := by
  letI : InnerProductSpace ℝ (WithLp 2 (Fin m → WithLp 2 (Fin n → ℝ))) := inferInstance
  refine
    { inner := fun A B ↦ inner ℝ (matrixToLp A) (matrixToLp B)
      norm_sq_eq_re_inner := ?_
      conj_inner_symm := ?_
      add_left := ?_
      smul_left := ?_ }
  · intro A
    change ‖matrixToLp A‖ ^ 2 = RCLike.re (inner ℝ (matrixToLp A) (matrixToLp A))
    exact norm_sq_eq_re_inner (matrixToLp A)
  · intro A B
    have h :
        star (inner ℝ (matrixToLp B) (matrixToLp A)) =
          inner ℝ (matrixToLp A) (matrixToLp B) := by
      simpa using (inner_conj_symm (𝕜 := ℝ) (matrixToLp A) (matrixToLp B))
    exact h
  · intro A B C
    simpa [matrixToLp] using inner_add_left (matrixToLp A) (matrixToLp B) (matrixToLp C)
  · intro A B r
    simpa [matrixToLp] using inner_smul_left (matrixToLp A) (matrixToLp B) r

variable {n : ℕ}

/-- The textbook space `𝕊^n` carries the Frobenius norm induced from ambient matrices. -/
instance : NormedAddCommGroup (symmetricMatrices n) := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) := Matrix.frobeniusNormedAddCommGroup
  exact inferInstance

/-- The scalar action on `𝕊^n` is compatible with the Frobenius norm. -/
instance : NormedSpace ℝ (symmetricMatrices n) := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) := Matrix.frobeniusNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := Matrix.frobeniusNormedSpace
  exact inferInstance

/-- The textbook Euclidean structure on `𝕊^n` is the Frobenius inner product inherited from
ambient matrices. -/
instance : InnerProductSpace ℝ (symmetricMatrices n) := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) := Matrix.frobeniusNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := Matrix.frobeniusNormedSpace
  letI : InnerProductSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := Matrix.frobeniusInnerProductSpace
  exact inferInstance

-- Proof sketch: combine `Matrix.frobenius_norm_def` with the specialization of
-- `matrixInner_eq_trace_transpose_mul` to `(A, A)`, then simplify the resulting self-pairing.
/-- The Frobenius norm of a real matrix is `√(Tr(Aᵀ A))`. -/
theorem frobenius_norm_eq_sqrt_trace_transpose_mul (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ = √(Matrix.trace (Aᵀ * A)) := sorry

-- Proof sketch: specialize the two Frobenius-pairing formulas from Definition 1.29 to `(A, A)`.
/-- The trace of `Aᵀ A` is the sum of the squares of the entries of `A`. -/
theorem trace_transpose_mul_eq_sum_sq_entries (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace (Aᵀ * A) = ∑ i, ∑ j, A i j ^ 2 := sorry

end
