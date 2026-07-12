import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_18
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Lemma_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped BigOperators

noncomputable section

section

variable {n : ℕ}

-- Proof sketch: identify the functional `y ↦ xᵀ y` with the continuous linear functional
-- `LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ x)` on `ℝ^n` equipped with the
-- `Q`-inner-product structure. By Fréchet-Riesz, its dual norm is the norm of the representing
-- vector `Q⁻¹ x`; then expand that norm using the quadratic-form formula.
/-- Proposition 1.10: if `ℝ^n` is endowed with the `Q`-norm associated to a positive definite
matrix `Q`, then the dual norm of the Euclidean pairing functional `y ↦ xᵀ y` is
`√(xᵀ Q⁻¹ x) = ‖x‖_{Q⁻¹}`. -/
theorem dual_qNorm_eq_sqrt_dotProduct_inv_mulVec
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (x : Fin n → ℝ) :
    letI := Q.toNormedAddCommGroup hQ
    letI := Q.toInnerProductSpace hQ.posSemidef
    dualNorm (dotProductBilin ℝ ℝ x) =
      Real.sqrt (dotProduct x (Q⁻¹.mulVec x)) := sorry

-- Proof sketch: specialize the quadratic-form expression for the norm induced by a positive
-- definite matrix to `Q = diagonal w`, then simplify `mulVec_diagonal` and `dotProduct`.
/-- For a diagonal positive definite matrix, the induced `Q`-norm is the weighted Euclidean norm
`√(∑ i, w i x_i^2)`. -/
theorem diagonal_qNorm_eq_sqrt_sum_weight_mul_sq
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (x : Fin n → ℝ) :
    @Norm.norm _ ((diagonal w).toNormedAddCommGroup (PosDef.diagonal hw)).toNorm x =
      Real.sqrt (∑ i, w i * x i ^ (2 : ℕ)) := sorry

-- Proof sketch: apply `dual_qNorm_eq_sqrt_dotProduct_inv_mulVec` with `Q = diagonal w`, rewrite
-- `(diagonal w)⁻¹` as the diagonal matrix with entries `w i` inverted, and simplify
-- `mulVec_diagonal` and `dotProduct`.
/-- For a diagonal positive definite matrix, the dual norm of the Euclidean pairing functional
`y ↦ xᵀ y` is `√(∑ i, (1 / w i) x_i^2)`. -/
theorem dual_diagonal_qNorm_eq_sqrt_sum_invWeight_mul_sq
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (x : Fin n → ℝ) :
    letI := (diagonal w).toNormedAddCommGroup (PosDef.diagonal hw)
    letI := (diagonal w).toInnerProductSpace (PosDef.diagonal hw).posSemidef
    dualNorm (dotProductBilin ℝ ℝ x) =
      Real.sqrt (∑ i, (w i)⁻¹ * x i ^ (2 : ℕ)) := sorry

end
