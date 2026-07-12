import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.Sheaf
import StacksProject_2024.Chap20.OpensInstances

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe u

section

local instance sheafPreadditive (Y : TopCat.{u}) : Preadditive (Y.Sheaf AddCommGrpCat.{u}) :=
  inferInstanceAs
    (Preadditive
      (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}))

/-- The top open is terminal in `Opens Y`. -/
private def topOpenIsTerminal (Y : TopCat.{u}) : IsTerminal (⊤ : Opens Y) :=
  IsTerminal.ofUniqueHom
    (fun V ↦ homOfLE (show V ≤ (⊤ : Opens Y) from by
      intro x hx
      trivial))
    fun V f ↦ Subsingleton.elim _ _

/-- The constant integer sheaf on `X`. The coefficient group is modeled by `ULift ℤ` to match the
ambient universe. -/
abbrev constantIntegerSheaf (X : TopCat.{u})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] :
    X.Sheaf AddCommGrpCat.{u} :=
  ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ)) : X.Sheaf AddCommGrpCat.{u})

/-- Additive maps from `ULift ℤ` are determined by the image of `1`. -/
private noncomputable def uliftIntAddHomEquiv (A : Type u) [AddCommGroup A] :
    (ULift.{u} ℤ →+ A) ≃ A where
  toFun f := f ⟨1⟩
  invFun a :=
    { toFun := fun n ↦ n.down • a
      map_zero' := by
        simp
      map_add' := by
        intro m n
        simp [add_zsmul] }
  left_inv f := by
    ext n
    have hn : (n.down : ℤ) • (⟨1⟩ : ULift.{u} ℤ) = n := by
      ext
      simp
    simpa [hn] using (map_zsmul f (n.down) (⟨1⟩ : ULift.{u} ℤ)).symm
  right_inv a := by
    simp

/-- Morphisms from `AddCommGrpCat.of (ULift ℤ)` are determined by the image of `1`. -/
private noncomputable def uliftIntObjectHomEquiv (A : AddCommGrpCat.{u}) :
    (AddCommGrpCat.of (ULift.{u} ℤ) ⟶ A) ≃ A where
  toFun f := (ConcreteCategory.hom f) ⟨1⟩
  invFun a :=
    AddCommGrpCat.ofHom <|
      (uliftIntAddHomEquiv A).symm a
  left_inv f := by
    ext n
    have hn : (n.down : ℤ) • (⟨1⟩ : ULift.{u} ℤ) = n := by
      ext
      simp
    simpa [hn] using
      (map_zsmul (ConcreteCategory.hom f) (n.down) (⟨1⟩ : ULift.{u} ℤ)).symm
  right_inv a := by
    change ((ConcreteCategory.hom
        (AddCommGrpCat.ofHom
          { toFun := fun n : ULift.{u} ℤ ↦ n.down • a
            map_zero' := by simp
            map_add' := by
              intro m n
              simp [add_zsmul] })) ⟨1⟩) = a
    simp

/-- Morphisms from `AddCommGrpCat.of (ULift ℤ)` are additively determined by the image of `1`. -/
private noncomputable def uliftIntObjectHomAddEquiv (A : AddCommGrpCat.{u}) :
    (AddCommGrpCat.of (ULift.{u} ℤ) ⟶ A) ≃+ A where
  toEquiv := uliftIntObjectHomEquiv A
  map_add' := by
    intro f g
    change (ConcreteCategory.hom (f + g)) ⟨1⟩ =
      (ConcreteCategory.hom f) ⟨1⟩ + (ConcreteCategory.hom g) ⟨1⟩
    rfl

/-- Morphisms from the constant integer sheaf on a space `Y` are equivalent to sections over the
top open. -/
noncomputable def constantIntegerSheaf_hom_equiv_top_section
    (Y : TopCat.{u})
    [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
    (G : Y.Sheaf AddCommGrpCat.{u}) :
    (constantIntegerSheaf Y ⟶ G) ≃ G.val.obj (Opposite.op (⊤ : Opens Y)) := by
  let adj :=
    CategoryTheory.constantSheafAdj
      (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
      (topOpenIsTerminal Y)
  simpa [constantIntegerSheaf] using
    (adj.homEquiv (AddCommGrpCat.of (ULift.{u} ℤ)) G).trans
      (uliftIntObjectHomEquiv (G.val.obj (Opposite.op (⊤ : Opens Y))))

/-- Morphisms from the constant integer sheaf on a space `Y` are additively equivalent to
sections over the top open. -/
noncomputable def constantIntegerSheaf_hom_addEquiv_top_section
    (Y : TopCat.{u})
    [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
    (G : Y.Sheaf AddCommGrpCat.{u}) :
    (constantIntegerSheaf Y ⟶ G) ≃+ G.val.obj (Opposite.op (⊤ : Opens Y)) where
  toEquiv := constantIntegerSheaf_hom_equiv_top_section Y G
  map_add' := by
    intro f g
    rfl

namespace CategoryTheory.Sheaf

/-- Global sections of an additive sheaf on a topological space identify additively with
morphisms from the constant integer sheaf. -/
noncomputable def globalSectionsAddEquivConstantIntegerSheafHom
    (Y : TopCat.{u})
    [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
    (G : Y.Sheaf AddCommGrpCat.{u}) :
    ((Γ (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj G) ≃+
      (constantIntegerSheaf Y ⟶ G) :=
  let eΓ :
      ((Γ (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj G) ≃+
        (((sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
          (Opposite.op (⊤ : Opens Y))).obj G) :=
    CategoryTheory.Iso.addCommGroupIsoToAddEquiv
      ((ΓNatIsoSheafSections
        (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}
        (topOpenIsTerminal Y)).app G)
  eΓ.trans (constantIntegerSheaf_hom_addEquiv_top_section Y G).symm

end CategoryTheory.Sheaf

end
