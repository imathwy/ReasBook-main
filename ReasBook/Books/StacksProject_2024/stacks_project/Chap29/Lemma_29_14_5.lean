import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_14_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable
  (P : {R T : Type u} → [CommRing R] → [CommRing T] → (R →+* T) → Prop)

/- Semantic recall / owner check:
- `lean_leansearch` surfaced the generic composition theorem
  `AlgebraicGeometry.HasRingHomProperty.stableUnderComposition` for affine-local scheme
  morphism properties coming from ring-map properties;
- `Definition_29_14_2.lean` and `Lemma_29_14_4.lean` fix the source-facing owner for this section
  as `LocallyOfType P`, so this item records the composition statement on that owner.
-/

/-- Lemma 29.14.5: let `P` be a property of ring maps. Assume `P` is local and stable under
composition. Then the composition of morphisms locally of type `P` is locally of type `P`. -/
@[stacks 01SV]
theorem locallyOfType_comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hP : RingHom.PropertyIsLocal P) (hcomp : RingHom.StableUnderComposition P)
    (hf : LocallyOfType P f) (hg : LocallyOfType P g) :
    LocallyOfType P (f ≫ g) := by
  rw [locallyOfType_iff_affineLocally P f hP] at hf
  rw [locallyOfType_iff_affineLocally P g hP] at hg
  rw [locallyOfType_iff_affineLocally P (f ≫ g) hP]
  letI : HasRingHomProperty (affineLocally P) P := HasRingHomProperty.mk hP rfl
  letI : (affineLocally P).IsStableUnderComposition :=
    HasRingHomProperty.stableUnderComposition hcomp
  simpa using MorphismProperty.comp_mem (affineLocally P) f g hf hg

end AlgebraicGeometry
