import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Forget
import Mathlib.RingTheory.DividedPowers.DPMorphism

open CategoryTheory
open DividedPowers

universe u

/-- A divided power ring is a commutative ring equipped with an ideal carrying divided powers. -/
structure DividedPowerRing where
  /-- The underlying commutative ring. -/
  carrier : Type u
  /-- The commutative ring structure on the underlying type. -/
  [commRing : CommRing carrier]
  /-- The distinguished ideal with divided powers. -/
  ideal : Ideal carrier
  /-- The divided power structure on the distinguished ideal. -/
  dividedPowers : DividedPowers ideal

attribute [instance] DividedPowerRing.commRing

instance : CoeSort DividedPowerRing (Type u) := ⟨DividedPowerRing.carrier⟩

namespace DividedPowerRing

/-- The bundled divided power ring attached to a commutative ring equipped with divided powers on
an ideal. -/
abbrev of (A : Type u) [CommRing A] (I : Ideal A) (hI : DividedPowers I) : DividedPowerRing :=
  ⟨A, I, hI⟩

/-- Morphisms of divided power rings are the canonical bundled divided power morphisms. -/
instance : Category DividedPowerRing where
  Hom A B := DPMorphism A.dividedPowers B.dividedPowers
  id A := DPMorphism.id A.dividedPowers
  comp f g := DPMorphism.comp g f
  id_comp := by
    intro A B f
    ext x
    rfl
  comp_id := by
    intro A B f
    ext x
    rfl
  assoc := by
    intro A B C D f g h
    ext x
    rfl

instance : ConcreteCategory DividedPowerRing
    (fun A B ↦ DPMorphism A.dividedPowers B.dividedPowers) where
  hom := fun f ↦ f
  ofHom := fun f ↦ f
  hom_ofHom := fun _ ↦ rfl
  ofHom_hom := fun _ ↦ rfl
  id_apply := fun _ ↦ rfl
  comp_apply := fun _ _ _ ↦ rfl

/-- A divided power morphism as a morphism in the category `DividedPowerRing`. -/
abbrev ofHom {A B : Type u} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B}
    {hI : DividedPowers I} {hJ : DividedPowers J} (f : DPMorphism hI hJ) :
    of A I hI ⟶ of B J hJ :=
  f

/-- The underlying commutative ring of a divided power ring. -/
abbrev toCommRingCat (A : DividedPowerRing) : CommRingCat :=
  CommRingCat.of A

instance : HasForget₂ DividedPowerRing CommRingCat :=
  { forget₂ :=
      { obj := toCommRingCat
        map := fun f ↦ CommRingCat.ofHom f.toRingHom
        map_id := by
          intro A
          ext x
          rfl
        map_comp := by
          intro A B C f g
          ext x
          rfl }
    forget_comp := rfl }

@[simp]
lemma forget₂_toCommRingCat_obj (A : DividedPowerRing) :
    (forget₂ DividedPowerRing CommRingCat).obj A = toCommRingCat A :=
  rfl

@[simp]
lemma forget₂_toCommRingCat_map {A B : DividedPowerRing} (f : A ⟶ B) :
    (forget₂ DividedPowerRing CommRingCat).map f = CommRingCat.ofHom f.toRingHom :=
  rfl

end DividedPowerRing
