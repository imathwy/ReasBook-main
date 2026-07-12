import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

-- Semantic recall: `lean_leansearch` found the canonical mathlib theorem
-- `AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom`. The source tag evidence is
-- consistent: item tag `01WN` agrees with the Stacks URL ending in `/tag/01WN`.

/-- Lemma 29.44.11: a morphism of schemes is finite if and only if it is affine and proper. -/
@[stacks 01WN]
theorem isFinite_iff_isAffineHom_and_isProper :
    IsFinite f ↔ IsAffineHom f ∧ IsProper f := sorry

end

end AlgebraicGeometry
