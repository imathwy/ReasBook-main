import StacksProject_2024.stacks_project.Chap13.Definition_13_8_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_16_Homotopy
import StacksProject_2024.stacks_project.Chap13.Lemma_13_10_6

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory

/-- The bounded-below homotopy-category lift of the ambient composite comparison is natural in the
source complex. -/
theorem mapBoundedBelowHomotopyCategoryCompHom_naturality
    {A B C : Type u} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (K L : K⁺(A)) (φ : K ⟶ L) :
    (mapBoundedBelowHomotopyCategory (F ⋙ G)).map φ ≫
      ObjectProperty.homMk ((Functor.mapHomotopyCategoryCompIso F G).hom.app L.obj) =
        ObjectProperty.homMk ((Functor.mapHomotopyCategoryCompIso F G).hom.app K.obj) ≫
          (mapBoundedBelowHomotopyCategory F ⋙ mapBoundedBelowHomotopyCategory G).map φ := sorry

/-- The bounded-below homotopy-category lift of the ambient composite comparison. -/
def mapBoundedBelowHomotopyCategoryCompHom
    {A B C : Type u} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    mapBoundedBelowHomotopyCategory (F ⋙ G) ⟶
      mapBoundedBelowHomotopyCategory F ⋙ mapBoundedBelowHomotopyCategory G :=
  NatTrans.mk
    (fun K ↦ ObjectProperty.homMk ((Functor.mapHomotopyCategoryCompIso F G).hom.app K.obj))
    (mapBoundedBelowHomotopyCategoryCompHom_naturality F G)

/-- The inverse bounded-below homotopy-category lift of the ambient composite comparison is
natural in the source complex. -/
theorem mapBoundedBelowHomotopyCategoryCompInv_naturality
    {A B C : Type u} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (K L : K⁺(A)) (φ : K ⟶ L) :
    (mapBoundedBelowHomotopyCategory F ⋙ mapBoundedBelowHomotopyCategory G).map φ ≫
      ObjectProperty.homMk ((Functor.mapHomotopyCategoryCompIso F G).inv.app L.obj) =
        ObjectProperty.homMk ((Functor.mapHomotopyCategoryCompIso F G).inv.app K.obj) ≫
          (mapBoundedBelowHomotopyCategory (F ⋙ G)).map φ := sorry

/-- The inverse bounded-below homotopy-category lift of the ambient composite comparison. -/
def mapBoundedBelowHomotopyCategoryCompInv
    {A B C : Type u} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    mapBoundedBelowHomotopyCategory F ⋙ mapBoundedBelowHomotopyCategory G ⟶
      mapBoundedBelowHomotopyCategory (F ⋙ G) :=
  NatTrans.mk
    (fun K ↦ ObjectProperty.homMk ((Functor.mapHomotopyCategoryCompIso F G).inv.app K.obj))
    (mapBoundedBelowHomotopyCategoryCompInv_naturality F G)

/-- The bounded-below homotopy-category lift of the ambient composite comparison has the expected
inverse. -/
theorem mapBoundedBelowHomotopyCategoryComp_hom_inv_id
    {A B C : Type u} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    mapBoundedBelowHomotopyCategoryCompHom F G ≫
      mapBoundedBelowHomotopyCategoryCompInv F G =
        𝟙 (mapBoundedBelowHomotopyCategory (F ⋙ G)) := sorry

/-- The inverse bounded-below homotopy-category lift of the ambient composite comparison has the
expected inverse. -/
theorem mapBoundedBelowHomotopyCategoryComp_inv_hom_id
    {A B C : Type u} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    mapBoundedBelowHomotopyCategoryCompInv F G ≫
      mapBoundedBelowHomotopyCategoryCompHom F G =
        𝟙 (mapBoundedBelowHomotopyCategory F ⋙ mapBoundedBelowHomotopyCategory G) := sorry

/-- Applying the bounded-below homotopy lift to an additive composite is canonically isomorphic
to composing the two bounded-below lifts. -/
def mapBoundedBelowHomotopyCategoryCompIso
    {A B C : Type u} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    mapBoundedBelowHomotopyCategory (F ⋙ G) ≅
      mapBoundedBelowHomotopyCategory F ⋙ mapBoundedBelowHomotopyCategory G where
  hom := mapBoundedBelowHomotopyCategoryCompHom F G
  inv := mapBoundedBelowHomotopyCategoryCompInv F G
  hom_inv_id := mapBoundedBelowHomotopyCategoryComp_hom_inv_id F G
  inv_hom_id := mapBoundedBelowHomotopyCategoryComp_inv_hom_id F G

end CategoryTheory
