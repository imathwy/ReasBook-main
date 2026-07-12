import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / owner check:
- `lean_leansearch` recalled the canonical scheme-morphism predicate `IsImmersion` and the
  target-local API `IsZariskiLocalAtTarget` for it.
- Mathlib's `morphismRestrict` notation `f ∣_ U` has type `(f ⁻¹ᵁ U).toScheme ⟶ U`, matching
  the source restriction `f|_{f^{-1}(U)} : f^{-1}(U) ⟶ U`.
-/

/-- Lemma 29.3.5: if every point of the source has a target-open neighbourhood on which the
restricted morphism is an immersion, then the original morphism is an immersion. -/
@[stacks 0FCZ]
theorem isImmersion_of_forall_exists_open_morphismRestrict
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : ∀ y : Y, ∃ U : X.Opens, f y ∈ U ∧ IsImmersion (f ∣_ U)) :
    IsImmersion f := sorry

end AlgebraicGeometry
