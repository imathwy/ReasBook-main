import Mathlib
import StacksProject_2024.stacks_project.Chap31.Lemma_31_15_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

-- Semantic recall: `lean_leansearch` surfaced
-- `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`, matching the source proof's
-- height-one-prime step. Following nearby Chapter 31 files, the closed subscheme is represented
-- by `D : X.IdealSheafData`, and the codimension-one hypothesis is expressed through the ambient
-- stalk at the image of the generic point of the integral subscheme.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- Lemma 31.15.7: let `X` be a locally Noetherian scheme and let `D ⊆ X` be an integral closed
subscheme. Assume that `D` has codimension `1` in `X`, expressed here by
`ringKrullDim (\mathcal O_{X,\xi}) = 1` at the image `\xi` of the generic point of `D`, and
assume that every local ring `\mathcal O_{X,x}` with `x ∈ D` is a unique factorization domain.
Then `D` is an effective Cartier divisor. -/
@[stacks 0AGA]
theorem isEffectiveCartierDivisor_of_stalks_uniqueFactorizationMonoid_of_genericPoint_ringKrullDim_eq_one
    (D : X.IdealSheafData) [IsIntegral D.subscheme]
    (hcodim : ringKrullDim (X.presheaf.stalk (D.subschemeι.base (genericPoint D.subscheme))) = 1)
    (hUFD : ∀ x : X, x ∈ D.support → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    D.IsEffectiveCartierDivisor := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
