import Mathlib
import StacksProject_2024.Chap29.Definition_29_4_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical closed-subscheme inclusion
-- `Scheme.IdealSheafData.inclusion`, its closed-immersion instance
-- `AlgebraicGeometry.instIsClosedImmersionInclusion`, and
-- `AlgebraicGeometry.isPullback_of_isClosedImmersion`. Local Definition 29.4.4 fixes the scheme
-- theoretic intersection as `(I ⊔ J).subscheme`.

variable {X : Scheme.{u}} (I J : X.IdealSheafData)

/-- Lemma 29.4.5 (1): the canonical morphism from the scheme theoretic intersection `Z ∩ Y` to the
first closed subscheme `Z` is a closed immersion. In the `IdealSheafData` owner, this is the
inclusion `(I ⊔ J).subscheme ⟶ I.subscheme`. -/
@[stacks 0C4I]
theorem schemeTheoreticIntersection_isClosedImmersion_fst :
    IsClosedImmersion (Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J)) := sorry

/-- Lemma 29.4.5 (2): the canonical morphism from the scheme theoretic intersection `Z ∩ Y` to the
second closed subscheme `Y` is a closed immersion. In the `IdealSheafData` owner, this is the
inclusion `(I ⊔ J).subscheme ⟶ J.subscheme`. -/
@[stacks 0C4I]
theorem schemeTheoreticIntersection_isClosedImmersion_snd :
    IsClosedImmersion (Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ I ⊔ J)) :=
  sorry

/-- Lemma 29.4.5 (3): the canonical square
`(I ⊔ J).subscheme ⟶ I.subscheme`, `(I ⊔ J).subscheme ⟶ J.subscheme`, `I.subscheme ⟶ X`,
`J.subscheme ⟶ X` is cartesian, i.e. the scheme theoretic intersection is the fibre product of
the two closed subscheme inclusions over `X`. -/
@[stacks 0C4I]
theorem schemeTheoreticIntersection_isPullback :
    IsPullback
      (Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ I ⊔ J))
      (Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J))
      J.subschemeι
      I.subschemeι := sorry

end AlgebraicGeometry
