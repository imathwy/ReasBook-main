import Mathlib
import StacksProject_2024.Chap29.Definition_29_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical affine-target-local owner
-- `targetAffineLocally`; local Chapter 29 precedent fixes the source-facing abbreviation
-- `QuasiAffineHom`, so this item is recorded as the direct composition-stability theorem for that
-- morphism property.

/-- Lemma 29.13.4: the composition of quasi-affine morphisms is quasi-affine. -/
@[stacks 01SN]
theorem QuasiAffineHom.comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : QuasiAffineHom f) (hg : QuasiAffineHom g) :
    QuasiAffineHom (f ≫ g) := sorry

end AlgebraicGeometry
