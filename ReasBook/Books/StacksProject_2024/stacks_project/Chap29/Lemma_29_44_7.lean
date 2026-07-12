import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

-- Semantic recall: `lean_leansearch` found the canonical mathlib theorem
-- `AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom`.  The source tag
-- evidence is consistent: item tag `01WM` agrees with the Stacks URL ending in `/tag/01WM`.

/-- Lemma 29.44.7: a morphism of schemes is integral if and only if it is affine and universally
closed. -/
@[stacks 01WM]
theorem isIntegralHom_iff_isAffineHom_and_universallyClosed :
    IsIntegralHom f ↔ IsAffineHom f ∧ UniversallyClosed f := sorry

end

end AlgebraicGeometry
