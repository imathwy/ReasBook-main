import Mathlib
import BauschkeLean.Chap24.Corollary_24_61
import BauschkeLean.Chap24.Corollary_24_65
import BauschkeLean.Chap24.Example_24_50
import BauschkeLean.Chap24.Proposition_24_63

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open ERealFunction
open scoped Gradient InnerProductSpace

noncomputable section

namespace ERealFunction

-- Domain-style sampling:
-- - primary domain: Chapter 24 spectral convex analysis for symmetric-matrix pullbacks of
--   coordinate-permutation-invariant penalties on `EuclideanSpace ℝ (Fin N)`.
-- - inspected owners:
--   `symmetricMatrixLocus` from `Proposition_24_60.lean`
--   `negativeBurgEntropyFinite` from `Example_24_50.lean`
--   `properSymmetricMatrixSpectralPullback` from `Corollary_24_61.lean`
--   `prox_symmetricMatrixSpectralPullback_eq_orthogonal_diagonal_prox` from
--   `Corollary_24_65.lean`
--   `gradientWithin` / `HasGradientWithinAt` from the Chapter 2 calculus-on-sets API
-- Source/core/bridge triage:
-- - `source-facing`: the log-determinant barrier `logDetBarrier`
-- - `core/canonical`: `symmetricMatrixSpectralPullback`
-- - `bridge/view`: `properSymmetricMatrixSpectralPullback`

private theorem negativeBurgEntropyFinite_effectiveDomain_nonempty {N : ℕ} :
    Set.Nonempty
      (effectiveDomain
        (negativeBurgEntropyFinite :
          EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal))) :=
  negativeBurgEntropyFinite_mem_gammaZero.2.nonempty

/-- Example 24.66 (1): the log-determinant barrier on real symmetric `N × N` matrices, viewed on
the Chapter 24 ambient Euclidean model, is the spectral pullback of the coordinatewise
negative-log barrier `φ(x) = -∑ i, log (x i)` on the strict positive orthant and `+∞`
elsewhere. -/
def logDetBarrier {N : ℕ} : SquareMatrixSpace N → Set.Ioi (⊥ : EReal) :=
  properSymmetricMatrixSpectralPullback
    negativeBurgEntropyFinite
    negativeBurgEntropyFinite_effectiveDomain_nonempty
    negativeBurgEntropyFinite_coordinatePermutationInvariant

/-- Coercing `logDetBarrier` back to `EReal` recovers the underlying spectral pullback owner. -/
@[simp] theorem logDetBarrier_apply {N : ℕ} (x : SquareMatrixSpace N) :
    (logDetBarrier x : EReal) =
      symmetricMatrixSpectralPullback negativeBurgEntropyFinite x := by
  simp [logDetBarrier]

/-- On a positive definite matrix, `logDetBarrier` evaluates to `-log (det A)`. -/
theorem logDetBarrier_apply_of_posDef {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef) :
    (logDetBarrier (matrixToEuclidean A) : EReal) = ((-Real.log A.det : ℝ) : EReal) :=
  sorry

/-- Off the positive-definite locus, `logDetBarrier` takes the value `+∞`. -/
theorem logDetBarrier_apply_of_not_posDef {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : ¬ A.PosDef) :
    (logDetBarrier (matrixToEuclidean A) : EReal) = ⊤ := sorry

/-- Example 24.66 (2): the log-determinant barrier belongs to `Γ₀(S^N)`. -/
theorem logDetBarrier_mem_gammaZero {N : ℕ} :
    logDetBarrier ∈ Γ₀(SquareMatrixSpace N) := by
  simpa [logDetBarrier] using
    (properSymmetricMatrixSpectralPullback_mem_gammaZero
      negativeBurgEntropyFinite
      negativeBurgEntropyFinite_effectiveDomain_nonempty
      negativeBurgEntropyFinite_coordinatePermutationInvariant
      negativeBurgEntropyFinite_mem_gammaZero)

/-- Example 24.66 (3): if `A = U (Diag λ(A)) Uᵀ` is an orthogonal diagonalization of a real
symmetric matrix `A`, then the proximal point of the log-determinant barrier at `A` is obtained
by conjugating the diagonal matrix with entries
`(λᵢ(A) + sqrt (λᵢ(A)^2 + 4)) / 2`. -/
theorem prox_logDetBarrier_eq_orthogonal_diagonal_positiveRoot
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian)
    (U : Matrix.orthogonalGroup (Fin N) ℝ)
    (hU :
      A = (U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal hA.eigenvalues *
            (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) :
    Prox[logDetBarrier, logDetBarrier_mem_gammaZero] (matrixToEuclidean A) =
      matrixToEuclidean
        ((U : Matrix (Fin N) (Fin N) ℝ) *
            Matrix.diagonal
              (fun i : Fin N ↦
                (hA.eigenvalues i + Real.sqrt (hA.eigenvalues i ^ (2 : ℕ) + 4)) / 2) *
            (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) := sorry

/-- Example 24.66 (4): the restriction of the log-determinant barrier to the symmetric-matrix
locus is differentiable at every positive definite matrix. -/
theorem differentiableWithinAt_logDetBarrier_of_posDef
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef) :
    DifferentiableWithinAt ℝ
      (fun x : SquareMatrixSpace N ↦ (logDetBarrier x : EReal).toReal)
      (symmetricMatrixLocus N)
      (matrixToEuclidean A) := sorry

/-- Example 24.66 (5): at a positive definite matrix, the canonical `gradientWithin` field of the
log-determinant barrier on the symmetric-matrix locus is `-A⁻¹`. -/
theorem gradientWithin_logDetBarrier_eq_neg_inv_of_posDef
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef) :
    gradientWithin
        (fun x : SquareMatrixSpace N ↦ (logDetBarrier x : EReal).toReal)
        (symmetricMatrixLocus N)
        (matrixToEuclidean A) =
      matrixToEuclidean (-A⁻¹) := sorry

end ERealFunction
