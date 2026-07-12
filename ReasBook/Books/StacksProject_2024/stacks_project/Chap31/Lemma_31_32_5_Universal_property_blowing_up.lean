import Mathlib
import StacksProject_2024.Chap31.Definition_31_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` recalled `ObjectProperty.FullSubcategory` for full
-- subcategories cut out by object predicates and `IsTerminal` for final objects.

/-- The full subcategory of `Over X` consisting of morphisms whose inverse image of the closed
subscheme defined by `I` is an effective Cartier divisor. -/
@[stacks 0806]
abbrev effectiveCartierPullbackOverCategory (X : Scheme.{u}) (I : X.IdealSheafData) :=
  ObjectProperty.FullSubcategory
    (fun Y : Over X ↦ IsEffectiveCartierDivisor (I.comap Y.hom))

/-- A blowup morphism, viewed as an object of the full subcategory where the inverse-image center
is an effective Cartier divisor. -/
@[stacks 0806]
abbrev blowupEffectiveCartierPullbackObject {X X' : Scheme.{u}} (I : X.IdealSheafData)
    (b : X' ⟶ X) [h : IsBlowup b I] : effectiveCartierPullbackOverCategory X I :=
  ObjectProperty.FullSubcategory.mk (Over.mk b)
    h.toIsEffectiveCartierDivisor

/-- Lemma 31.32.5 (Universal property blowing up): let `X` be a scheme and let `Z ⊆ X` be the
closed subscheme defined by `I`. In the full subcategory of `(Sch/X)` consisting of morphisms
whose inverse image of `Z` is an effective Cartier divisor, the blowing up `b : X' ⟶ X` of `Z`
in `X` is a final object. -/
@[stacks 0806]
def blowupEffectiveCartierPullbackObject_isTerminal {X X' : Scheme.{u}}
    (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] :
    IsTerminal (blowupEffectiveCartierPullbackObject I b) := sorry

/-- Companion uniqueness form for the terminality of the blowup object in the effective-Cartier
pullback subcategory. -/
theorem blowupEffectiveCartierPullbackObject_isTerminal_from_eq {X X' : Scheme.{u}}
    (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (Y : effectiveCartierPullbackOverCategory X I)
    (f : Y ⟶ blowupEffectiveCartierPullbackObject I b) :
    f = (blowupEffectiveCartierPullbackObject_isTerminal I b).from Y := sorry

end AlgebraicGeometry
