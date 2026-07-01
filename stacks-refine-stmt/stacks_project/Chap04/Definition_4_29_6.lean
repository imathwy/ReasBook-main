import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace StrictPseudofunctor

/-- Two strict `2`-functors are inverse when they are mutually inverse on objects,
`1`-morphisms, and `2`-morphisms. The morphism identities are expressed using heterogeneous
equality because the inverse-object equalities need not be definitional. -/
structure IsInverse
    {B : Type u₁} [Bicategory.{w₁, v₁} B] [Bicategory.Strict B]
    {C : Type u₂} [Bicategory.{w₂, v₂} C] [Bicategory.Strict C]
    (F : StrictPseudofunctor B C) (G : StrictPseudofunctor C B) : Prop where
  left_obj : ∀ X : B, G.obj (F.obj X) = X
  left_map : ∀ ⦃X Y : B⦄ (f : X ⟶ Y), G.map (F.map f) ≍ f
  left_map₂ : ∀ ⦃X Y : B⦄ {f g : X ⟶ Y} (η : f ⟶ g), G.map₂ (F.map₂ η) ≍ η
  right_obj : ∀ X : C, F.obj (G.obj X) = X
  right_map : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map (G.map f) ≍ f
  right_map₂ : ∀ ⦃X Y : C⦄ {f g : X ⟶ Y} (η : f ⟶ g), F.map₂ (G.map₂ η) ≍ η

end StrictPseudofunctor

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] [Bicategory.Strict B]

/-- The strict slice `2`-category of a strict `2`-category `B` above a fixed object `X`. Its
objects are arrows into `X`, its `1`-morphisms are strictly commuting triangles, and its
`2`-morphisms are `2`-cells over the identity of `X`. -/
@[ext]
structure SliceTwoCategory (X : B) where
  obj : B
  hom : obj ⟶ X

namespace SliceTwoCategory

variable {X : B}

/-- A `1`-morphism in the slice strict `2`-category over `X`. -/
@[ext]
structure Hom (S T : SliceTwoCategory X) where
  hom : S.obj ⟶ T.obj
  comm : hom ≫ T.hom = S.hom

/-- A `2`-morphism in the slice strict `2`-category over `X`. -/
@[ext]
structure TwoHom {S T : SliceTwoCategory X} (F G : Hom S T) where
  hom : F.hom ⟶ G.hom
  comm : hom ▷ T.hom ≫ eqToHom G.comm = eqToHom F.comm

private def idHom (S : SliceTwoCategory X) : Hom S S where
  hom := 𝟙 S.obj
  comm := by simp

private def compHom {S T U : SliceTwoCategory X} (F : Hom S T) (G : Hom T U) : Hom S U where
  hom := F.hom ≫ G.hom
  comm := by
    simp [Category.assoc, F.comm, G.comm]

private def idTwoHom {S T : SliceTwoCategory X} (F : Hom S T) : TwoHom F F where
  hom := 𝟙 F.hom
  comm := by
    simpa using congrArg (fun α ↦ α ≫ eqToHom F.comm) (id_whiskerRight F.hom T.hom)

private def compTwoHom {S T : SliceTwoCategory X} {F G H : Hom S T}
    (η : TwoHom F G) (θ : TwoHom G H) : TwoHom F H where
  hom := η.hom ≫ θ.hom
  comm := by
    sorry

instance (S T : SliceTwoCategory X) : Category (Hom S T) where
  Hom F G := TwoHom F G
  id := idTwoHom
  comp := compTwoHom
  id_comp := by
    sorry
  comp_id := by
    sorry
  assoc := by
    sorry

private def whiskerLeftTwoHom {S T U : SliceTwoCategory X} (F : Hom S T) {G H : Hom T U}
    (η : TwoHom G H) : TwoHom (compHom F G) (compHom F H) where
  hom := F.hom ◁ η.hom
  comm := by
    sorry

private def whiskerRightTwoHom {S T U : SliceTwoCategory X} {F G : Hom S T}
    (η : TwoHom F G) (H : Hom T U) : TwoHom (compHom F H) (compHom G H) where
  hom := η.hom ▷ H.hom
  comm := by
    sorry

private def associatorIso {R S T U : SliceTwoCategory X}
    (F : Hom R S) (G : Hom S T) (H : Hom T U) :
    compHom (compHom F G) H ≅ compHom F (compHom G H) where
  hom :=
    { hom := (α_ F.hom G.hom H.hom).hom
      comm := by
        sorry }
  inv :=
    { hom := (α_ F.hom G.hom H.hom).inv
      comm := by
        sorry }

private def leftUnitorIso {S T : SliceTwoCategory X} (F : Hom S T) :
    compHom (idHom S) F ≅ F where
  hom :=
    { hom := (λ_ F.hom).hom
      comm := by
        sorry }
  inv :=
    { hom := (λ_ F.hom).inv
      comm := by
        sorry }

private def rightUnitorIso {S T : SliceTwoCategory X} (F : Hom S T) :
    compHom F (idHom T) ≅ F where
  hom :=
    { hom := (ρ_ F.hom).hom
      comm := by
        sorry }
  inv :=
    { hom := (ρ_ F.hom).inv
      comm := by
        sorry }

instance : Bicategory (SliceTwoCategory X) where
  Hom S T := Hom S T
  homCategory S T := inferInstance
  id := idHom
  comp := compHom
  whiskerLeft := whiskerLeftTwoHom
  whiskerRight := whiskerRightTwoHom
  associator := associatorIso
  leftUnitor := leftUnitorIso
  rightUnitor := rightUnitorIso
  whisker_exchange := by
    sorry
  whiskerLeft_id := by
    sorry
  whiskerLeft_comp := by
    sorry
  id_whiskerLeft := by
    sorry
  comp_whiskerLeft := by
    sorry
  id_whiskerRight := by
    sorry
  comp_whiskerRight := by
    sorry
  whiskerRight_id := by
    sorry
  whiskerRight_comp := by
    sorry
  whisker_assoc := by
    sorry
  pentagon := by
    sorry
  triangle := by
    sorry

instance : Bicategory.Strict (SliceTwoCategory X) where
  id_comp := by
    sorry
  comp_id := by
    sorry
  assoc := by
    sorry
  leftUnitor_eqToIso := by
    sorry
  rightUnitor_eqToIso := by
    sorry
  associator_eqToIso := by
    sorry

end SliceTwoCategory

end CategoryTheory
