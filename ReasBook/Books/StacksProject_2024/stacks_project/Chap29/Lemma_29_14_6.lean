import Mathlib
import StacksProject_2024.Chap29.Definition_29_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S S' : Scheme.{u}} {f : X ⟶ S}
variable
  (P : {R T : Type u} → [CommRing R] → [CommRing T] → (R →+* T) → Prop)

/- Semantic recall / owner check:
- `lean_leansearch` surfaced the ring-level base-change owner
  `RingHom.IsStableUnderBaseChange` and the scheme-level bridge
  `AlgebraicGeometry.HasRingHomProperty.isStableUnderBaseChange`;
- Chapter 29 already fixes the source-facing local owner as `LocallyOfType P f`, so the present
  item is recorded directly on that owner for the base-changed morphism `pullback.snd f g`.
-/

/-- Lemma 29.14.6: if `P` is a local property of ring maps and is stable under base change, then
the base change of a morphism locally of type `P` is again locally of type `P`. -/
@[stacks 01SW]
theorem locallyOfType_pullback_snd
    (hP : RingHom.PropertyIsLocal P)
    (hbc : RingHom.IsStableUnderBaseChange P)
    (hf : LocallyOfType P f) (g : S' ⟶ S) :
    LocallyOfType P (pullback.snd f g) := by
  rw [locallyOfType_iff_affineLocally P f hP] at hf
  letI : HasRingHomProperty (affineLocally P) P := ⟨hP, rfl⟩
  letI : (affineLocally P).IsStableUnderBaseChange :=
    HasRingHomProperty.isStableUnderBaseChange hbc
  exact (locallyOfType_iff_affineLocally P (pullback.snd f g) hP).2 <|
    MorphismProperty.pullback_snd f g hf

end AlgebraicGeometry
