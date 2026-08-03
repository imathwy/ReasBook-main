import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap24.Corollary_24_61
import BauschkeLean.Chap24.Proposition_24_58

open ERealFunction

section

variable {N : ℕ}
variable (φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal))
variable (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
variable (hφsymm : CoordinatePermutationInvariant φ)

-- Semantic recall/local precedent: `lean_leansearch` only surfaced unrelated generic proximity
-- results, so this item uses the Chapter 12 scaled-prox notation together with the Chapter 24
-- spectral-pullback API on the ambient Euclidean matrix model.

/-- If `φ ∈ Γ₀(ℝ^N)` is symmetric, then its packaged Fenchel conjugate `φ∗[hφ]` is symmetric as a
`]-∞,+∞]`-valued function as well. -/
theorem gammaZeroConjugate_coordinatePermutationInvariant
    (φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (hφsymm : CoordinatePermutationInvariant φ)
    :
    CoordinatePermutationInvariant (φ∗[hφ]) := by
  intro σ x
  apply Subtype.ext
  simpa [gammaZeroConjugate_apply] using
    ERealFunction.conjugate_coordinatePermutationInvariant hφsymm σ x

/-- The canonical packaged spectral pullback of the Fenchel conjugate `φ∗[hφ]`. -/
noncomputable abbrev properSymmetricMatrixSpectralPullbackConjugate
    (φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (hφsymm : CoordinatePermutationInvariant φ) :
    SquareMatrixSpace N → Set.Ioi (⊥ : EReal) :=
  properSymmetricMatrixSpectralPullback
    (φ∗[hφ])
    (gammaZeroConjugate_mem_gammaZero hφ).2.nonempty
    (gammaZeroConjugate_coordinatePermutationInvariant φ hφ hφsymm)

/-- The canonical packaged spectral pullback of `φ∗[hφ]` belongs to `Γ₀(S^N)`. -/
theorem properSymmetricMatrixSpectralPullbackConjugate_mem_gammaZero
    (φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (hφsymm : CoordinatePermutationInvariant φ) :
    properSymmetricMatrixSpectralPullbackConjugate φ hφ hφsymm ∈ Γ₀(SquareMatrixSpace N) :=
  properSymmetricMatrixSpectralPullback_mem_gammaZero
    (φ∗[hφ])
    (gammaZeroConjugate_mem_gammaZero hφ).2.nonempty
    (gammaZeroConjugate_coordinatePermutationInvariant φ hφ hφsymm)
    (gammaZeroConjugate_mem_gammaZero hφ)

/-- Corollary 24.62: if `φ ∈ Γ₀(ℝ^N)` is symmetric, if `γ ∈ ℝ_{++}`, and if `A` is a real
symmetric `N × N` matrix, then the proximity operator of the spectral pullback `φ ∘ λ`, expressed
on the ambient Euclidean matrix model `SquareMatrixSpace N`, satisfies Moreau's decomposition
with the spectral pullback of the Fenchel conjugate `φ*`. Since the owner is canonically extended
by `⊤` off the symmetric locus, the displayed identity holds for every ambient matrix
representative `A`. -/
theorem symmetricMatrixSpectralPullback_prox_eq_sub_scaledProx_conjugate
    (φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (hφsymm : CoordinatePermutationInvariant φ)
    (γ : PosReal) (A : Matrix (Fin N) (Fin N) ℝ) :
    Prox[
      γ,
      properSymmetricMatrixSpectralPullback φ hφ.2.nonempty hφsymm,
      properSymmetricMatrixSpectralPullback_mem_gammaZero φ hφ.2.nonempty hφsymm hφ
    ] (matrixToEuclidean A) =
      matrixToEuclidean A -
        (γ : ℝ) • Prox[
          (γ⁻¹ : PosReal),
          properSymmetricMatrixSpectralPullbackConjugate φ hφ hφsymm,
          properSymmetricMatrixSpectralPullbackConjugate_mem_gammaZero φ hφ hφsymm
        ]
          ((γ : ℝ)⁻¹ • matrixToEuclidean A) := sorry

end
