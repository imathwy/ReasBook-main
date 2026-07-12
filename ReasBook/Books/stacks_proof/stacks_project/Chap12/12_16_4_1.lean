import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable (A B : GradedObjectWithShift (1 : ℤ) C) (k : ℤ)

/- Domain-style sampling for `12.16.4.1`:
- primary domain: shifts of graded objects and the induced bijections on Hom sets;
- sampled owner declarations:
  `shiftEquiv`,
  `Adjunction.homEquiv`,
  `GradedObject.shiftFunctor_obj_apply`,
  `ShiftedHom`;
- best owner abstraction: the shift autoequivalence
  `shiftEquiv (GradedObjectWithShift (1 : ℤ) C) k`;
- primitive data: only the canonical shift autoequivalence on graded objects;
- derived API: the textbook bijection `Hom(A, B[k]) ≃ Hom(A[-k], B)`.

Source/core/bridge triage:
- `core/canonical`: `shiftEquiv` on `GradedObjectWithShift (1 : ℤ) C`;
- `bridge/view`: the induced Hom equivalence obtained from its adjunction;
- `source-facing`: the textbook bijection between morphisms into a shift and morphisms out of the
  opposite shift.

This item should therefore remain a direct canonical check of the owner-induced equivalence, not a
new local wrapper. -/
/-- 12.16.4.1: the canonical shift autoequivalence induces the textbook bijection
`Hom(A, B[k]) ≃ Hom(A[-k], B)`. -/
-- The inverse shift autoequivalence gives the canonical Hom equivalence in the opposite
-- orientation, and taking its symmetric form matches the textbook statement.
abbrev hom_into_shift_equiv : (A ⟶ B⟦k⟧) ≃ (A⟦-k⟧ ⟶ B) :=
  (((shiftEquiv _ k).symm.toAdjunction.homEquiv A B).symm)

end

end CategoryTheory
