import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_50_1
import StacksProject_2024.stacks_project.Chap31.Lemma_31_15_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

-- Semantic recall: `lean_leansearch` surfaced the ring-theoretic height-at-most-one owner
-- `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing`, while local Chapter 29
-- precedent packages “generic point of an irreducible component” as membership in
-- `genericPointsOfIrreducibleComponents`. The source point `ξ` is therefore a point of the closed
-- subscheme `D.subscheme`, and the conclusion is stated on the ambient stalk at `D.subschemeι.base ξ`.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- Lemma 31.15.3 (1): let `X` be a locally Noetherian scheme and let `D ⊆ X` be a locally
principal closed subscheme. If `ξ` is a generic point of an irreducible component of the closed
subscheme `D`, then the ambient local ring `\mathcal O_{X,\xi}` has Krull dimension at most `1`.
-/
theorem stalk_ringKrullDim_le_one_of_isLocallyPrincipal_of_mem_genericPointsOfIrreducibleComponents
    (D : X.IdealSheafData) (hD : IsLocallyPrincipalClosedSubscheme D.subschemeι) {ξ : D.subscheme}
    (hξ : ξ ∈ genericPointsOfIrreducibleComponents D.subscheme) :
    ringKrullDim (X.presheaf.stalk (D.subschemeι.base ξ)) ≤ 1 := sorry

/-- Lemma 31.15.3 (2): let `X` be a locally Noetherian scheme and let `D ⊆ X` be an effective
Cartier divisor. If `ξ` is a generic point of an irreducible component of the closed subscheme
`D`, then the ambient local ring `\mathcal O_{X,\xi}` has Krull dimension exactly `1`. -/
theorem stalk_ringKrullDim_eq_one_of_isEffectiveCartierDivisor_of_mem_genericPointsOfIrreducibleComponents
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] {ξ : D.subscheme}
    (hξ : ξ ∈ genericPointsOfIrreducibleComponents D.subscheme) :
    ringKrullDim (X.presheaf.stalk (D.subschemeι.base ξ)) = 1 := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
