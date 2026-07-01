import FirstOrderMethodsinOptimization.Chap01.Definition_1_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix RealInnerProductSpace

section

variable {m n k : ℕ}

-- Proof sketch: expand the coordinate formula for `𝒜 X`, rewrite the Euclidean inner product with
-- `y` using `euclideanSpace_inner_eq_sum_mul`, and use linearity of `Matrix.trace` to identify the
-- resulting sum with the Frobenius pairing against `∑ i, y i • A i`.
/-- Proposition 1.13: if a linear map from `ℝ^{m × n}` to `ℝ^k` is given coordinatewise by the
trace pairings `X ↦ Tr(A_iᵀ X)`, then the matrix `∑ i, y_i A_i` satisfies the defining adjoint
identity against the canonical Euclidean inner product on `ℝ^k` and the Frobenius pairing on
`ℝ^{m × n}`. -/
theorem matrix_trace_representation_adjoint
    {𝒜 : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
    {A : Fin k → Matrix (Fin m) (Fin n) ℝ}
    (h𝒜 : ∀ X i, 𝒜 X i = Matrix.trace ((A i)ᵀ * X))
    (X : Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin k)) :
    ⟪𝒜 X, y⟫ = Matrix.trace (((∑ i, y i • A i)ᵀ) * X) := sorry

/-- Sum-form companion to `matrix_trace_representation_adjoint`. -/
theorem matrix_trace_representation_adjoint_spec
    {𝒜 : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
    {A : Fin k → Matrix (Fin m) (Fin n) ℝ}
    (h𝒜 : ∀ X i, 𝒜 X i = Matrix.trace ((A i)ᵀ * X))
    (X : Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin k)) :
    ∑ i, (𝒜 X) i * y i = Matrix.trace (((∑ i, y i • A i)ᵀ) * X) := by
  simpa [euclideanSpace_inner_eq_sum_mul] using
    matrix_trace_representation_adjoint h𝒜 X y

end
