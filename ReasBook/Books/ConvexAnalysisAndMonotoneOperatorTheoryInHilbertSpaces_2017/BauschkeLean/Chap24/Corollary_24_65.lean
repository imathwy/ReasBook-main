import Mathlib
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap24.Proposition_24_63

open Matrix
open ERealFunction

-- Semantic recall/local precedent: `lean_leansearch` only surfaced generic spectral-theorem
-- owners, so this item stays on the local Chapter 24 spectral-pullback API together with the
-- Chapter 12 proximal-operator owner `Prox[_, _]`.

-- Source/core/bridge triage:
-- `source-facing`: this corollary states the explicit spectral proximal formula attached to an
--   orthogonal diagonalization of `A`.
-- `core/canonical`: the underlying owner is `symmetricMatrixSpectralPullback`.
-- `bridge/view`: `properSymmetricMatrixSpectralPullback` is used only to place that owner in the
--   Chapter 12 `Prox` interface.

section

variable {N : ℕ}
variable (φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal))
variable (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
variable (hφsymm : CoordinatePermutationInvariant φ)

/-- Corollary 24.65: if `φ ∈ Γ₀(ℝ^N)` is symmetric, if `A` is a real symmetric `N × N` matrix,
and if `U` is an orthogonal matrix satisfying `A = U (Diag λ(A)) Uᵀ`, then the proximity
operator of the spectral pullback `φ ∘ λ` at `A` is the conjugate by `U` of the diagonal matrix
whose diagonal is `Prox_φ (λ(A))`. -/
theorem prox_symmetricMatrixSpectralPullback_eq_orthogonal_diagonal_prox
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian)
    (U : Matrix.orthogonalGroup (Fin N) ℝ)
    (hU :
      A = (↑U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal hA.eigenvalues *
            (↑U : Matrix (Fin N) (Fin N) ℝ)ᵀ) :
    Prox[
      properSymmetricMatrixSpectralPullback φ hφ.2.nonempty hφsymm,
      properSymmetricMatrixSpectralPullback_mem_gammaZero φ hφ.2.nonempty hφsymm hφ
    ] (matrixToEuclidean A) =
      matrixToEuclidean
        ((↑U : Matrix (Fin N) (Fin N) ℝ) *
            Matrix.diagonal
              ((EuclideanSpace.equiv (Fin N) ℝ)
                (Prox[φ, hφ] (symmetricMatrixEigenvalues hA))) *
            (↑U : Matrix (Fin N) (Fin N) ℝ)ᵀ) := sorry

end
