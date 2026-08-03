import BauschkeLean.Chap17.Proposition_17_45
import BauschkeLean.Chap24.Corollary_24_61
import BauschkeLean.Chap24.Fact_24_59

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped ERealFunction Gradient InnerProductSpace

noncomputable section

-- Semantic recall/local precedent: `lean_leansearch` surfaced only generic spectral-theorem and
-- gradient owners, so this item follows the local Chapter 24 owner
-- `symmetricMatrixSpectralPullback`, the shared-diagonalization owner
-- `theobald_trace_eq_eigenvalues_dotProduct_iff`, and the Chapter 17
-- differentiability/subgradient surface on the Euclidean matrix model.

section

variable {N : ℕ}
variable (φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal))

/-- Proposition 24.63 (1): for a symmetric `φ ∈ Γ₀(ℝ^N)` and real symmetric matrices `A` and
`B`, the spectral pullback and its conjugate satisfy the source Fenchel--Young equality at `A` and
`B`, together with the corresponding eigenvalue pairing bound. -/
theorem spectral_pullback_eq_add_conjugate_and_eigenvalue_pairing_le
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (hφsymm : CoordinatePermutationInvariant φ)
    (A B : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (symmetricMatrixSpectralPullback φ (matrixToEuclidean A) : EReal) +
        ERealFunction.conjugate (symmetricMatrixSpectralPullback φ) (matrixToEuclidean B) =
      (φ (symmetricMatrixEigenvalues hA) : EReal) +
        ERealFunction.conjugate (Function.asEReal φ) (symmetricMatrixEigenvalues hB) ∧
      ((⟪symmetricMatrixEigenvalues hA, symmetricMatrixEigenvalues hB⟫_ℝ : ℝ) : EReal) ≤
        (φ (symmetricMatrixEigenvalues hA) : EReal) +
          ERealFunction.conjugate (Function.asEReal φ) (symmetricMatrixEigenvalues hB) := sorry

/-- Companion to Proposition 24.63 (1): the spectral pullback and its conjugate evaluate at
Hermitian matrices by the corresponding eigenvalue formulas. -/
theorem spectral_pullback_eq_add_conjugate
    (hφsymm : CoordinatePermutationInvariant φ)
    (A B : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (symmetricMatrixSpectralPullback φ (matrixToEuclidean A) : EReal) +
        ERealFunction.conjugate (symmetricMatrixSpectralPullback φ) (matrixToEuclidean B) =
      (φ (symmetricMatrixEigenvalues hA) : EReal) +
        ERealFunction.conjugate (Function.asEReal φ) (symmetricMatrixEigenvalues hB) := sorry

/-- Companion to Proposition 24.63 (1): the ordered eigenvalue pairing satisfies the
Fenchel--Young bound attached to `φ` and its conjugate. -/
theorem eigenvalue_pairing_le_add_conjugate
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (A B : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((⟪symmetricMatrixEigenvalues hA, symmetricMatrixEigenvalues hB⟫_ℝ : ℝ) : EReal) ≤
      (φ (symmetricMatrixEigenvalues hA) : EReal) +
        ERealFunction.conjugate (Function.asEReal φ) (symmetricMatrixEigenvalues hB) := sorry

/- Proposition 24.63 (2): the Theobald trace bound is exactly the current-repository owner
`theobald_trace_le_eigenvalues_dotProduct`. -/
#check theobald_trace_le_eigenvalues_dotProduct

/-- Proposition 24.63 (3): for a symmetric `φ ∈ Γ₀(ℝ^N)` and real symmetric matrices `A` and
`B`, `B` is a subgradient of the spectral pullback at `A` exactly when the eigenvalue vector of
`B` is a subgradient of `φ` at the eigenvalue vector of `A` and one orthogonal matrix diagonalizes
both matrices with those canonical eigenvalue lists. -/
theorem mem_subdifferential_symmetricMatrixSpectralPullback_iff
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (hφsymm : CoordinatePermutationInvariant φ)
    (A B : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    matrixToEuclidean B ∈ (∂ (symmetricMatrixSpectralPullback φ)) (matrixToEuclidean A) ↔
      symmetricMatrixEigenvalues hB ∈ (∂ φ) (symmetricMatrixEigenvalues hA) ∧
        ∃ U : Matrix.orthogonalGroup (Fin N) ℝ,
          A = (U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal hA.eigenvalues *
                (U : Matrix (Fin N) (Fin N) ℝ)ᵀ ∧
            B = (U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal hB.eigenvalues *
                  (U : Matrix (Fin N) (Fin N) ℝ)ᵀ := sorry

/-- Proposition 24.63 (4): for a symmetric `φ ∈ Γ₀(ℝ^N)` and a real symmetric matrix `A`, the
subdifferential of the spectral pullback at `A`, transported back to matrices, is exactly the set
of orthogonal conjugates of diagonal matrices built from subgradients of `φ` at the eigenvalue
vector of `A`, using an orthogonal diagonalization of `A` itself. -/
theorem image_subdifferential_symmetricMatrixSpectralPullback_eq
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (hφsymm : CoordinatePermutationInvariant φ)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    euclideanToMatrix '' ((∂ (symmetricMatrixSpectralPullback φ)) (matrixToEuclidean A)) =
      {B : Matrix (Fin N) (Fin N) ℝ |
        ∃ U : Matrix.orthogonalGroup (Fin N) ℝ,
          ∃ y ∈ (∂ φ) (symmetricMatrixEigenvalues hA),
            A = (U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal hA.eigenvalues *
                  (U : Matrix (Fin N) (Fin N) ℝ)ᵀ ∧
              B = (U : Matrix (Fin N) (Fin N) ℝ) *
                    Matrix.diagonal ((EuclideanSpace.equiv (Fin N) ℝ) y) *
                    (U : Matrix (Fin N) (Fin N) ℝ)ᵀ} := sorry

/-- Proposition 24.63 (5): for a symmetric `φ ∈ Γ₀(ℝ^N)` and a real symmetric matrix `A`, the
spectral pullback is differentiable at `A` exactly when `φ` is differentiable at the eigenvalue
vector of `A`; in that case, every orthogonal diagonalization of `A` yields the source gradient
formula `(24.124)`. -/
theorem differentiableAt_symmetricMatrixSpectralPullback_iff_and_gradient_eq
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (hφsymm : CoordinatePermutationInvariant φ)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    (DifferentiableAt ℝ
        (fun x : SquareMatrixSpace N ↦ (symmetricMatrixSpectralPullback φ x).toReal)
        (matrixToEuclidean A) ↔
      DifferentiableAt ℝ
        (fun x : EuclideanSpace ℝ (Fin N) ↦ (φ x : EReal).toReal)
        (symmetricMatrixEigenvalues hA)) ∧
      (DifferentiableAt ℝ
          (fun x : EuclideanSpace ℝ (Fin N) ↦ (φ x : EReal).toReal)
          (symmetricMatrixEigenvalues hA) →
        ∀ U : Matrix.orthogonalGroup (Fin N) ℝ,
          A = (U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal hA.eigenvalues *
                (U : Matrix (Fin N) (Fin N) ℝ)ᵀ →
            ∇ (fun x : SquareMatrixSpace N ↦ (symmetricMatrixSpectralPullback φ x).toReal)
                (matrixToEuclidean A) =
              matrixToEuclidean
                ((U : Matrix (Fin N) (Fin N) ℝ) *
                    Matrix.diagonal
                      ((EuclideanSpace.equiv (Fin N) ℝ)
                        (∇ (fun x : EuclideanSpace ℝ (Fin N) ↦ (φ x : EReal).toReal)
                          (symmetricMatrixEigenvalues hA))) *
                    (U : Matrix (Fin N) (Fin N) ℝ)ᵀ)) := sorry

/-- Companion to Proposition 24.63 (5): differentiability of the spectral pullback at a Hermitian
matrix is equivalent to differentiability of `φ` at the corresponding eigenvalue vector. -/
theorem differentiableAt_symmetricMatrixSpectralPullback_iff
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (hφsymm : CoordinatePermutationInvariant φ)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    DifferentiableAt ℝ
      (fun x : SquareMatrixSpace N ↦ (symmetricMatrixSpectralPullback φ x).toReal)
      (matrixToEuclidean A) ↔
      DifferentiableAt ℝ
        (fun x : EuclideanSpace ℝ (Fin N) ↦ (φ x : EReal).toReal)
        (symmetricMatrixEigenvalues hA) :=
  (differentiableAt_symmetricMatrixSpectralPullback_iff_and_gradient_eq φ hφ hφsymm A hA).1

/-- Companion to Proposition 24.63 (5): every orthogonal diagonalization of a Hermitian matrix
realizes the gradient of the spectral pullback by conjugating the diagonal matrix of coordinate
gradients of `φ`. -/
theorem gradient_symmetricMatrixSpectralPullback_eq
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (hφsymm : CoordinatePermutationInvariant φ)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian)
    (hφdiff : DifferentiableAt ℝ
      (fun x : EuclideanSpace ℝ (Fin N) ↦ (φ x : EReal).toReal)
      (symmetricMatrixEigenvalues hA))
    (U : Matrix.orthogonalGroup (Fin N) ℝ)
    (hU : A = (U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal hA.eigenvalues *
      (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) :
    ∇ (fun x : SquareMatrixSpace N ↦ (symmetricMatrixSpectralPullback φ x).toReal)
        (matrixToEuclidean A) =
      matrixToEuclidean
        ((U : Matrix (Fin N) (Fin N) ℝ) *
            Matrix.diagonal
              ((EuclideanSpace.equiv (Fin N) ℝ)
                (∇ (fun x : EuclideanSpace ℝ (Fin N) ↦ (φ x : EReal).toReal)
                  (symmetricMatrixEigenvalues hA))) *
            (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) :=
  (differentiableAt_symmetricMatrixSpectralPullback_iff_and_gradient_eq φ hφ hφsymm A hA).2
    hφdiff U hU

end
