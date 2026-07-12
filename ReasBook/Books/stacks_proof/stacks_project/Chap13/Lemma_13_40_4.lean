import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import StacksProject_2024.Chap13.Definition_13_40_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe v u

namespace CategoryTheory.ObjectProperty

/- Domain-style sampling for Lemma 13.40.4:
- primary domain: orthogonals of object properties and their induced full subcategories in
  categories with zero morphisms and, later, triangulated structure;
- sampled core/canonical declarations:
  `ObjectProperty.rightOrthogonal`,
  `ObjectProperty.leftOrthogonal`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsTriangulated`;
- best owner abstraction: the source-facing owners are the orthogonal object properties `A^⊥` and
  `^⊥A`; retract stability and triangulatedity are derived owner instances on those object
  properties, while the full-subcategory realizations are bridge/view consequences;
- primitive data: only the object property `A : ObjectProperty D`;
- derived API: the retract-stability instances below, strict-fullness from canonical
  isomorphism-closure instances, and the induced full-subcategory triangulated structures coming
  from the owner-level orthogonal `IsTriangulated` instances.

Source/core/bridge triage:
- `source-facing`: the saturation statements for the right and left orthogonals;
- `core/canonical`: the owner object properties `A^⊥`, `^⊥A`, and the generic predicates
  `ObjectProperty.IsStableUnderRetracts` and `CategoryTheory.IsTriangulated`;
- `bridge/view`: the full-subcategory realizations of the orthogonals.

There is no extra local wrapper to keep here: the file should prove retract stability directly for
the canonical orthogonal owners and otherwise reuse the upstream instance machinery verbatim. -/

section Saturated

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
variable (A : ObjectProperty D)

-- Proof sketch: if `X` is a retract of `Y` and `Y` lies in `A^⊥`, then any map
-- `B ⟶ X` with `A B` factors through the retract inclusion `X ⟶ Y`; applying the retract
-- projection `Y ⟶ X` to the resulting zero morphism shows the original map is zero.
/-- Lemma 13.40.4 (1): the right orthogonal `A^⊥` is stable under retracts, hence
is saturated; in the triangulated setting recalled below, it is also a triangulated object
property, so its canonical full subcategory carries the induced triangulated structure. -/
@[stacks 0FXC]
instance :
    A^⊥.IsStableUnderRetracts where
  of_retract h hY := by
    intro B f hB
    have hf : f ≫ h.i = 0 := hY (f ≫ h.i) hB
    calc
      f = (f ≫ h.i) ≫ h.r := by
        rw [Category.assoc, h.retract, Category.comp_id]
      _ = 0 := by rw [hf, zero_comp]

-- Proof sketch: dually, if `X` is a retract of `Y` and `Y` lies in `^⊥A`, then any
-- map `X ⟶ B` with `A B` factors through the retract projection `Y ⟶ X`, so it vanishes because
-- every map out of `Y` into an object of `A` is zero.
/-- Lemma 13.40.4 (2): the left orthogonal `^⊥A` is stable under retracts, hence is
saturated; in the triangulated setting recalled below, it is also a triangulated object property,
so its canonical full subcategory carries the induced triangulated structure. -/
@[stacks 0FXC]
instance :
    (^⊥A).IsStableUnderRetracts where
  of_retract h hY := by
    intro B f hB
    have hf : h.r ≫ f = 0 := hY (h.r ≫ f) hB
    calc
      f = h.i ≫ (h.r ≫ f) := by
        rw [← Category.assoc, h.retract, Category.id_comp]
      _ = 0 := by rw [hf, comp_zero]

/- Companion recall: orthogonals are strictly full because they are canonically closed under
isomorphisms. -/
#check (inferInstance : A^⊥.IsClosedUnderIsomorphisms)

/- Companion recall: the same strict-fullness statement holds for the left orthogonal. -/
#check (inferInstance : (^⊥A).IsClosedUnderIsomorphisms)

end Saturated

section Triangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (A : ObjectProperty D) [A.IsStableUnderShift ℤ]

/- Companion recall: in the triangulated-subcategory sense, the right orthogonal is itself a
canonical triangulated object property. -/
#check (inferInstance : (A^⊥).IsTriangulated)

/- Companion recall: the left orthogonal is likewise a canonical triangulated object property. -/
#check (inferInstance : (^⊥A).IsTriangulated)

end Triangulated

end CategoryTheory.ObjectProperty
