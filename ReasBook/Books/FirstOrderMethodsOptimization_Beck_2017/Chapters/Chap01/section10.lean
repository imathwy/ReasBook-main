import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_10 (from Chap01) -/
universe u

open WithLp
open scoped RealInnerProductSpace

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 1.10: for a nonzero normal vector `a`, the hyperplane with normal vector `a` and
offset `b` is the affine subspace of points whose inner product with `a` is `b`. The defining
formula is canonical and extends to arbitrary `a`. -/
noncomputable def hyperplane (a : E) (b : ℝ) : AffineSubspace ℝ E :=
  (affineSpan ℝ ({b} : Set ℝ)).comap (((innerSL ℝ a).toLinearMap).toAffineMap)

-- Proof sketch: unfold `hyperplane`; membership in the defining set is exactly the displayed
-- inner-product equation.
/-- A point `x` lies in `hyperplane a b` exactly when its inner product with `a` is `b`. -/
@[simp] theorem mem_hyperplane_iff (a : E) (b : ℝ) (x : E) :
    x ∈ hyperplane a b ↔ ⟪a, x⟫ = b :=
  by
    rw [hyperplane, AffineSubspace.mem_comap]
    simp

section

variable {ι : Type*} [Fintype ι]

/-- The Chapter 1 hyperplane owner transported to the coordinate model `ι → ℝ` through the
canonical `L²` equivalence `toLp 2`. -/
noncomputable def coordinateHyperplane (a : ι → ℝ) (b : ℝ) : Set (ι → ℝ) :=
  (toLp 2) ⁻¹' (hyperplane (toLp 2 a) b : Set (EuclideanSpace ℝ ι))

-- Proof sketch: membership in the pulled-back hyperplane is membership in the Euclidean
-- hyperplane, which is the inner-product equation `⟪toLp 2 a, toLp 2 x⟫ = b`; the standard
-- `toLp` inner-product bridge identifies that equation with `dotProduct a x = b`.
/-- A coordinate vector `x` lies in `coordinateHyperplane a b` exactly when
`dotProduct a x = b`. -/
@[simp] theorem mem_coordinateHyperplane_iff (a x : ι → ℝ) (b : ℝ) :
    x ∈ coordinateHyperplane a b ↔ dotProduct a x = b := by
  change toLp 2 x ∈ hyperplane (toLp 2 a) b ↔ dotProduct a x = b
  rw [mem_hyperplane_iff]
  rw [show inner ℝ (toLp 2 a) (toLp 2 x) = dotProduct a x by
    simpa [dotProduct_comm] using (EuclideanSpace.inner_toLp_toLp a x)]

end

end

/-! ### Proposition_1_10 (from Chap01) -/
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
