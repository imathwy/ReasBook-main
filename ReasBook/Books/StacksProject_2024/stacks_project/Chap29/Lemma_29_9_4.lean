import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section

variable {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

-- Semantic recall: `lean_leansearch` found the exact scheme-morphism base-change instance
-- `AlgebraicGeometry.Surjective.instSndScheme`, so this item is a pure canonical recall rather
-- than a redundant local wrapper.

/- Lemma 29.9.4: the base change of a surjective morphism is surjective. This is exactly the
canonical scheme-morphism base-change instance `AlgebraicGeometry.Surjective.instSndScheme`,
asserting that if `f : X ⟶ Z` is surjective then `pullback.snd f g : pullback f g ⟶ Y` is
surjective for every `g : Y ⟶ Z`. -/
recall AlgebraicGeometry.Surjective.instSndScheme
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Surjective f] :
    Surjective (pullback.snd f g)

end

end AlgebraicGeometry
