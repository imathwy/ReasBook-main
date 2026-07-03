import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_15 (from Chap01) -/
section

variable (n : ℕ)

/- Definition 1.15 is source-facing: the textbook coordinate space `ℝ^n` is represented by the
coordinate model `Fin n → ℝ`, while the canonical mathlib owner for this Euclidean coordinate
space is `EuclideanSpace ℝ (Fin n)`, identified with the coordinate model by
`EuclideanSpace.equiv`. -/
#check (Fin n → ℝ)
#check (EuclideanSpace ℝ (Fin n))
#check (EuclideanSpace.equiv (Fin n) ℝ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ))

/- The standard basis of `ℝ^n` is the canonical orthonormal basis
`EuclideanSpace.basisFun (Fin n) ℝ`. -/
#check EuclideanSpace.basisFun (Fin n) ℝ

variable (i : Fin n)

/- The `i`th standard basis vector is the `i`th vector of `EuclideanSpace.basisFun (Fin n) ℝ`,
and `EuclideanSpace.basisFun_apply` identifies it with `EuclideanSpace.single i 1`. -/
#check (EuclideanSpace.basisFun (Fin n) ℝ i : EuclideanSpace ℝ (Fin n))
#check (EuclideanSpace.basisFun_apply (Fin n) ℝ i :
  EuclideanSpace.basisFun (Fin n) ℝ i = EuclideanSpace.single i 1)

/- The textbook vectors `e` and `0` are the constant-one and zero vectors in the coordinate
model `Fin n → ℝ`; via `EuclideanSpace.equiv (Fin n) ℝ`, these are the corresponding vectors in
`EuclideanSpace ℝ (Fin n)`. -/
#check ((EuclideanSpace.equiv (Fin n) ℝ).symm 1 : EuclideanSpace ℝ (Fin n))
#check ((EuclideanSpace.equiv (Fin n) ℝ).symm 0 : EuclideanSpace ℝ (Fin n))

end

/-! ### Proposition_1_15 (from Chap01) -/
/- Proposition 1.15: whenever a square matrix `A` is invertible, the transpose of `⅟A` is the
inverse of `Aᵀ`, which is the canonical mathlib formulation of `(A^T)^{-1} = (A^{-1})^T`. -/
recall Matrix.transpose_invOf
