import Mathlib
import StacksProject_2024.stacks_project.Chap31.Lemma_31_32_5_Universal_property_blowing_up

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.comap_id` for identity
-- pullback of ideal sheaves, and nearby Chapter 31 files expose the blowup universal property via
-- `effectiveCartierPullbackOverCategory` and `IsTerminal`.

section

variable (X : Scheme.{u}) (I : X.IdealSheafData) [IsEffectiveCartierDivisor I]

/-- Pulling back an effective Cartier divisor along the identity morphism gives an effective
Cartier divisor. -/
theorem isEffectiveCartierDivisor_comap_id :
    IsEffectiveCartierDivisor (I.comap (𝟙 X)) := sorry

/-- Lemma 31.32.7: Let `X` be a scheme. Let `Z ⊆ X` be an effective Cartier divisor. The blowup
of `X` in `Z` is the identity morphism of `X`, formalized as terminality of the identity object
in the effective-Cartier pullback category. -/
@[stacks 0807]
def identityEffectiveCartierPullbackObject_isTerminal :
    IsTerminal
      ((ObjectProperty.FullSubcategory.mk (Over.mk (𝟙 X))
        (isEffectiveCartierDivisor_comap_id X I)) :
          effectiveCartierPullbackOverCategory X I) := sorry

/-- Companion uniqueness form for the terminality of the identity object in the
effective-Cartier pullback subcategory. -/
theorem identityEffectiveCartierPullbackObject_isTerminal_from_eq
    (Y : effectiveCartierPullbackOverCategory X I)
    (f : Y ⟶ ((ObjectProperty.FullSubcategory.mk (Over.mk (𝟙 X))
      (isEffectiveCartierDivisor_comap_id X I)) :
        effectiveCartierPullbackOverCategory X I)) :
    f = (identityEffectiveCartierPullbackObject_isTerminal X I).from Y := sorry

end

end AlgebraicGeometry
