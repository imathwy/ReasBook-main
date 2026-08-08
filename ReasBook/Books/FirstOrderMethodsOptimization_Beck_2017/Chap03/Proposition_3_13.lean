import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_17

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped Gradient Matrix

noncomputable section

section

variable {m : ℕ}

-- Internal elaboration bridge to the owner theorem `FiniteDimensional.complete` for the
-- `H`-weighted normed-space structure induced by `Matrix.toNormedAddCommGroup`.
private theorem posDefMatrixCompleteSpace (H : Matrix (Fin m) (Fin m) ℝ) (hH : H.PosDef) :
    @CompleteSpace (Fin m → ℝ) (H.toNormedAddCommGroup hH).toUniformSpace := by
  sorry

variable (H : Matrix (Fin m) (Fin m) ℝ) (hH : H.PosDef)

/- Proposition 3.13 is a `bridge/view` item in the chapter calculus API. The source-facing input is
the Euclidean Fréchet derivative represented by `D`, while the weighted Hilbert-space owners are
`Matrix.toNormedAddCommGroup`, `Matrix.toInnerProductSpace`, and the canonical completeness result
`FiniteDimensional.complete`. -/

-- Proof sketch: under the `H`-weighted inner product, the derivative functional `v ↦ dotProduct D
-- v` is exactly the Riesz image of `(H⁻¹).mulVec D`. First transfer the Euclidean `HasFDerivAt`
-- hypothesis to the equivalent `H`-weighted norm, then apply the `HasFDerivAt`/`HasGradientAt`
-- bridge in that weighted inner-product structure.

/-- Proposition 3.13: if the Fréchet derivative of `f` at `x` is represented by `D` through the
standard Euclidean dot product on `ℝ^m`, then replacing the inner product by
`⟪u, v⟫ = dotProduct u (H.mulVec v)` for a positive definite matrix `H` changes the gradient to
`(H⁻¹).mulVec D`. -/
theorem hasGradientAt_inv_mulVec_of_posDef_matrix_inner
    {f : (Fin m → ℝ) → ℝ} {x D : Fin m → ℝ}
    (hD : HasFDerivAt f (LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ D)) x) :
    letI := H.toNormedAddCommGroup hH
    letI := H.toInnerProductSpace hH.posSemidef
    letI := posDefMatrixCompleteSpace H hH
    HasGradientAt f ((H⁻¹).mulVec D) x := by
  sorry

-- Proof sketch: apply `HasGradientAt.gradient` to
-- `hasGradientAt_inv_mulVec_of_posDef_matrix_inner`.
/-- The totalized gradient for the `H`-weighted inner product agrees with the vector
`(H⁻¹).mulVec D` whenever the derivative is the Euclidean pairing functional
`v ↦ dotProduct D v`. -/
theorem gradient_eq_inv_mulVec_of_posDef_matrix_inner
    {f : (Fin m → ℝ) → ℝ} {x D : Fin m → ℝ}
    (hD : HasFDerivAt f (LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ D)) x) :
    letI := H.toNormedAddCommGroup hH
    letI := H.toInnerProductSpace hH.posSemidef
    letI := posDefMatrixCompleteSpace H hH
    gradient f x = (H⁻¹).mulVec D := by
  letI := H.toNormedAddCommGroup hH
  letI := H.toInnerProductSpace hH.posSemidef
  letI := posDefMatrixCompleteSpace H hH
  exact (hasGradientAt_inv_mulVec_of_posDef_matrix_inner H hH hD).gradient

end
