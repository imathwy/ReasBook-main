import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

namespace AlgebraicGeometry

section

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism composition instance
-- `AlgebraicGeometry.instSurjectiveCompScheme`, so this item is a pure canonical recall rather
-- than a redundant local wrapper.
/- Lemma 29.9.2: the composition of surjective morphisms is surjective. This is a direct recall of
mathlib's instance `AlgebraicGeometry.instSurjectiveCompScheme`. -/
recall AlgebraicGeometry.instSurjectiveCompScheme
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [Surjective g] :
    Surjective (f ≫ g)

end

end AlgebraicGeometry
