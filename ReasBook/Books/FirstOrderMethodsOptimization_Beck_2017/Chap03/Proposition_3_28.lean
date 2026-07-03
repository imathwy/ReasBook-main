import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_19
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

/- Proposition 3.28 is `source-facing` in the chapter spectral-subdifferential API. The
matrix-side owner declarations are `symmetricMaxEigenvalue` and
`symmetricRankOne_mem_euclideanSubdifferentialAt_symmetricMaxEigenvalue` from Proposition 3.4,
while the chapter bridge/view owner is `euclideanSubdifferentialAt` from Theorem 3.4. The affine
transport step is governed upstream by `subdifferential_precompose_affineMap_subset` from
Theorem 3.19. For the coefficient family `A : Fin m → 𝕊^n`, the owner linear combination map is
the mathlib Pi-map `LinearMap.lsum`, transported from `(Fin m → ℝ)` to `ℝ^m`; the displayed
subgradient vector is then the source-facing coordinate view of the adjoint pullback of the
rank-one matrix subgradient. -/

section

open Matrix InnerProductSpace
open WithLp (linearEquiv)

variable {m n : ℕ}

local notation "Em" => EuclideanSpace ℝ (Fin m)
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "𝕊" => symmetricMatrices n

recall euclideanSubdifferentialAt
recall subdifferential_precompose_affineMap_subset
recall symmetricRankOne_mem_euclideanSubdifferentialAt_symmetricMaxEigenvalue
recall LinearMap.lsum
recall LinearMap.adjoint

/-- The canonical linear map `x ↦ ∑ i, xᵢ Aᵢ` from `ℝ^m` to the space `𝕊^n` of real symmetric
matrices. -/
noncomputable def symmetricMatrixLinearMap (A : Fin m → 𝕊) : Em →ₗ[ℝ] 𝕊 :=
  (LinearMap.lsum ℝ (fun _ : Fin m ↦ ℝ) ℝ
      (fun i ↦ (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (A i))).comp
    (linearEquiv 2 ℝ (Fin m → ℝ)).toLinearMap

-- Proof sketch: `LinearMap.lsum` is the owner linear map sending a coordinate family
-- `z : Fin m → ℝ` to `∑ i, z i • Aᵢ`; precomposing with the canonical `WithLp` linear equivalence
-- `EuclideanSpace ℝ (Fin m) ≃ₗ[ℝ] (Fin m → ℝ)` gives the desired map on `ℝ^m`.
/-- Evaluating `symmetricMatrixLinearMap A` gives the linear combination `∑ i, xᵢ Aᵢ`. -/
@[simp] theorem symmetricMatrixLinearMap_apply (A : Fin m → 𝕊) (x : Em) :
    symmetricMatrixLinearMap A x = ∑ i, x i • A i := by
  simp [symmetricMatrixLinearMap]

section

variable [NeZero n]

/-- The maximum-eigenvalue objective obtained by composing `symmetricMaxEigenvalue` with the affine
map `x ↦ A₀ + ∑ i, xᵢ Aᵢ`. -/
noncomputable def affine_symmetric_max_eigenvalue
    (A0 : 𝕊) (A : Fin m → 𝕊) : Em → ℝ :=
  fun x ↦ symmetricMaxEigenvalue (A0 + symmetricMatrixLinearMap A x)

-- Proof sketch: unfold `affine_symmetric_max_eigenvalue`; by definition it is
-- `symmetricMaxEigenvalue` applied to `A₀ + symmetricMatrixLinearMap A x`.
/-- The affine maximum-eigenvalue objective is `x ↦ λ_max (A₀ + ∑ i, xᵢ Aᵢ)`. -/
@[simp] theorem affine_symmetric_max_eigenvalue_def
    (A0 : 𝕊) (A : Fin m → 𝕊) (x : Em) :
    affine_symmetric_max_eigenvalue A0 A x =
      symmetricMaxEigenvalue (A0 + symmetricMatrixLinearMap A x) :=
  rfl

end

/-- The vector in `ℝ^m` whose `i`-th coordinate is the quadratic form
`yᵀ Aᵢ y`. -/
noncomputable def affine_symmetric_max_eigenvalue_subgradient_vector
    (A : Fin m → 𝕊) (y : En) : Em :=
  (symmetricMatrixLinearMap A).adjoint (symmetricRankOne y)

-- Proof sketch: `affine_symmetric_max_eigenvalue_subgradient_vector A y` is the adjoint pullback
-- of the matrix-side rank-one subgradient `yyᵀ`. Evaluating that pullback on the `i`-th standard
-- coordinate vector identifies the `i`-th coordinate with the quadratic form `yᵀ Aᵢ y`.
/-- The coordinates of `affine_symmetric_max_eigenvalue_subgradient_vector A y` are the
quadratic-form
values `yᵀ Aᵢ y`. -/
@[simp] theorem affine_symmetric_max_eigenvalue_subgradient_vector_apply
    (A : Fin m → 𝕊) (y : En) (i : Fin m) :
    affine_symmetric_max_eigenvalue_subgradient_vector A y i =
      dotProduct y (A i *ᵥ y) := by
  sorry

section

variable [NeZero n]

-- Proof sketch: combine the matrix-side statement that a unit eigenvector for the largest
-- eigenvalue yields the rank-one subgradient `yyᵀ` of `λ_max` with the affine transformation rule
-- for subdifferentials along `x ↦ A₀ + ∑ i, xᵢ Aᵢ`. Evaluating the pulled-back symmetric-matrix
-- subgradient against each coordinate direction identifies the resulting vector with
-- `(yᵀ A₁ y, …, yᵀ A_m y)`.
/-- Proposition 3.28: if `y` is a normalized eigenvector of
`A₀ + ∑ i, xᵢ Aᵢ` for its maximum eigenvalue, then the vector whose coordinates are the quadratic
forms `yᵀ Aᵢ y` belongs to the Euclidean subdifferential of
`x ↦ λ_max (A₀ + ∑ i, xᵢ Aᵢ)` at `x`. -/
theorem affine_symmetric_max_eigenvalue_subgradient_vector_mem_subdifferential_at
    (A0 : 𝕊) (A : Fin m → 𝕊) (x : Em) (y : En)
    (hy_norm : ‖y‖ = 1)
    (hy_eigen : (A0 + symmetricMatrixLinearMap A x : Matrix (Fin n) (Fin n) ℝ) *ᵥ y =
        affine_symmetric_max_eigenvalue A0 A x • y) :
    affine_symmetric_max_eigenvalue_subgradient_vector A y ∈
      euclideanSubdifferentialAt (affine_symmetric_max_eigenvalue A0 A) x := sorry

end

end
