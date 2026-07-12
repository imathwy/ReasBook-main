import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

-- Semantic recall: `lean_leansearch` found the canonical owner
-- `AlgebraicGeometry.IsAffineHom` and the exact composition instance
-- `AlgebraicGeometry.instIsAffineHomCompScheme`. This item is therefore a pure canonical recall,
-- matching the existing chapter style for composition-stability facts.
/-
Lemma 29.11.8: the composition of affine morphisms is affine. This is a direct recall of
mathlib's instance `AlgebraicGeometry.instIsAffineHomCompScheme`.
-/
recall AlgebraicGeometry.instIsAffineHomCompScheme

section

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsAffineHom f] [IsAffineHom g]

#check (inferInstance : IsAffineHom (f ≫ g))

end
