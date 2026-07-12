import Mathlib
import StacksProject_2024.Chap29.Definition_29_15_1
import StacksProject_2024.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall / analogue check:
-- - `lean_leansearch` recalled the canonical owner `AlgebraicGeometry.IsClosedImmersion` together
--   with its affine / stalk-surjectivity interfaces;
-- - local Chapter 29 precedent records source-side “of finite type” and “of finite presentation”
--   through `Scheme.Hom.FiniteType` and `Scheme.Hom.FinitePresentation`;
-- - the Stacks source assumption “bijective on points” is kept explicit as bijectivity of the
--   underlying map on points of `g.base`, rather than being compressed into a separate owner.

/-- Lemma 29.45.7: let `f : X ⟶ S` and `g : S' ⟶ S` be morphisms of schemes. Assume `g` is a
closed immersion, `g` is bijective on points, the base change projection
`pullback.snd f g : pullback f g ⟶ S'` is a closed immersion, and either `f` is of finite type or
`g` is of finite presentation. Then `f` is a closed immersion. -/
@[stacks 0896]
theorem isClosedImmersion_of_pullbackSnd_of_bijectiveOnPoints_closedImmersion
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (hg : IsClosedImmersion g)
    (hg_bij : Function.Bijective ⇑(ConcreteCategory.hom g.base))
    (hpullback : IsClosedImmersion (pullback.snd f g))
    (hfinite : Scheme.Hom.FiniteType f ∨ Scheme.Hom.FinitePresentation g) :
    IsClosedImmersion f := sorry

end AlgebraicGeometry
