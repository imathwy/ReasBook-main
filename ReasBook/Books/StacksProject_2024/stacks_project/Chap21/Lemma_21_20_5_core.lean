import Mathlib
import StacksProject_2024.Chap19.AdditiveFunctorTotalRightDerived
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap21.Lemma_21_19_1_core

open CategoryTheory
open ComplexShape
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

local notation "Mod(" X ")" => ModuleCat X
local notation "DMod(" X ")" => ModuleDerived X
local notation "Qis(" X ")" => ModuleQis X

/-- The ring `Γ(\mathcal C, \mathcal O_X)` of global sections of the structure sheaf of a
ringed site. -/
abbrev globalSectionsRing (X : RingedSite.{u, v}) : RingCat.{max u v} :=
  RingCat.of (RingCat.sectionsSubring X.structureSheaf.obj)

local notation "ΓMod(" X ")" => _root_.ModuleCat (globalSectionsRing X)

private abbrev globalSectionsRingPresheaf (X : RingedSite.{u, v}) :
    Xᵒᵖ ⥤ RingCat.{max u v} :=
  (Functor.const Xᵒᵖ).obj (globalSectionsRing X)

private def globalSectionsRingHom (X : RingedSite.{u, v}) :
    globalSectionsRingPresheaf X ⟶ X.structureSheaf.obj where
  app U := RingCat.ofHom
    { toFun := fun s ↦ s.1 U
      map_one' := rfl
      map_mul' := by
        intro x y
        rfl
      map_zero' := rfl
      map_add' := by
        intro x y
        rfl }
  naturality := by
    intro Y Z f
    ext s
    exact (s.2 f).symm

private abbrev moduleGlobalSectionsPresheaf (X : RingedSite.{u, v}) :
    Mod(X) ⥤ PresheafOfModules (globalSectionsRingPresheaf X) where
  obj ℱ := (PresheafOfModules.restrictScalars (globalSectionsRingHom X)).obj ℱ.val
  map f := (PresheafOfModules.restrictScalars (globalSectionsRingHom X)).map f.val
  map_id ℱ := by
    ext U x
    rfl
  map_comp f g := by
    ext U x
    rfl

private abbrev moduleGlobalSectionsDiagram (X : RingedSite.{u, v}) (ℱ : Mod(X)) :
    Xᵒᵖ ⥤ ΓMod(X) where
  obj U := ((moduleGlobalSectionsPresheaf X).obj ℱ).obj U
  map f := ((moduleGlobalSectionsPresheaf X).obj ℱ).map f
  map_id U := by
    simpa using ((moduleGlobalSectionsPresheaf X).obj ℱ).map_id U
  map_comp f g := by
    simpa using ((moduleGlobalSectionsPresheaf X).obj ℱ).map_comp f g

private abbrev moduleGlobalSectionsObject (X : RingedSite.{u, v}) (ℱ : Mod(X)) : ΓMod(X) :=
  _root_.ModuleCat.of (globalSectionsRing X)
    (_root_.ModuleCat.sectionsSubmodule (moduleGlobalSectionsDiagram X ℱ))

/-- The `Γ(\mathcal C,\mathcal O_X)`-module-valued global-sections functor on
`\mathcal O_X`-modules. -/
abbrev moduleGlobalSectionsFunctor (X : RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [X.siteTopology.HasSheafCompose
      (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})] :
    Mod(X) ⥤ ΓMod(X) where
  obj ℱ := moduleGlobalSectionsObject X ℱ
  map {ℱ 𝒢} f := _root_.ModuleCat.ofHom
    { toFun := fun s ↦
        let fΓ := (moduleGlobalSectionsPresheaf X).map f
        let tΓ := PresheafOfModules.sectionsMap fΓ ⟨s.1, s.2⟩
        ⟨tΓ.1, tΓ.2⟩
      map_add' := by
        intro s t
        let fΓ := (moduleGlobalSectionsPresheaf X).map f
        ext U
        change
          (fΓ.app U).hom (s.1 U + t.1 U) =
            (fΓ.app U).hom (s.1 U) + (fΓ.app U).hom (t.1 U)
        exact map_add (fΓ.app U).hom (s.1 U) (t.1 U)
      map_smul' := by
        intro a s
        let fΓ := (moduleGlobalSectionsPresheaf X).map f
        ext U
        let M : ΓMod(X) := ((moduleGlobalSectionsPresheaf X).obj ℱ).obj U
        let N : ΓMod(X) := ((moduleGlobalSectionsPresheaf X).obj 𝒢).obj U
        let _ : AddCommGroup ↑M := M.isAddCommGroup
        let _ : Module (globalSectionsRing X) ↑M := M.isModule
        let _ : AddCommGroup ↑N := N.isAddCommGroup
        let _ : Module (globalSectionsRing X) ↑N := N.isModule
        let fU : M ⟶ N := fΓ.app U
        let x : M := s.1 U
        change fU.hom (a • x) = a • fU.hom x
        exact fU.hom.map_smul a x }
  map_id ℱ := by
    rfl
  map_comp f g := by
    rfl

/-- The additive global-sections functor on `\mathcal O_X`-modules, computed on the underlying
abelian sheaf. -/
abbrev moduleGlobalSectionsAdditiveFunctor (X : RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}] :
    Mod(X) ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    Sheaf.Γ X.siteTopology AddCommGrpCat.{max u v}

/-- Forgetting the `Γ(\mathcal C,\mathcal O_X)`-module structure on global sections recovers the
additive global-sections functor. -/
theorem moduleGlobalSectionsForget_eq (X : RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [X.siteTopology.HasSheafCompose
      (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})] :
    moduleGlobalSectionsFunctor X ⋙
        forget₂ (_root_.ModuleCat (globalSectionsRing X)) AddCommGrpCat.{max u v} =
      moduleGlobalSectionsAdditiveFunctor X := by
  sorry

instance moduleGlobalSectionsAdditiveFunctor_additive (X : RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}] :
    (moduleGlobalSectionsAdditiveFunctor X).Additive := by
  sorry

/-- The functor on homotopy categories induced by global sections on module sheaves. -/
abbrev moduleGlobalSectionsToDerived (X : RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
    [(moduleGlobalSectionsAdditiveFunctor X).Additive] :=
  mapHomotopyCategoryToDerived (moduleGlobalSectionsAdditiveFunctor X)

/-- The unbounded right derived global-sections functor on module sheaves. -/
noncomputable abbrev moduleGlobalSectionsDerived (X : RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
    [(moduleGlobalSectionsAdditiveFunctor X).Additive]
    [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (Qis(X))] :
    DMod(X) ⥤ DerivedCategory AddCommGrpCat.{max u v} :=
  Functor.totalRightDerived (moduleGlobalSectionsToDerived X)
    (DerivedCategory.Qh :
      HomotopyCategory (Mod(X)) (up ℤ) ⥤ DerivedCategory (Mod(X)))
    (Qis(X))

/-- The sections functor over a fixed object of a ringed site is additive. -/
instance moduleSectionsEvaluation_additive (X : RingedSite.{u, v}) (U : X) :
    (SheafOfModules.evaluation X.structureSheaf (op U)).Additive := by
  sorry

/-- The functor on homotopy categories induced by sections over a fixed object. -/
abbrev moduleSectionsToDerived (X : RingedSite.{u, v}) (U : X) :
    HomotopyCategory (Mod(X)) (up ℤ) ⥤
      DerivedCategory (_root_.ModuleCat (X.structureSheaf.1.obj (op U))) :=
  mapHomotopyCategoryToDerived (SheafOfModules.evaluation X.structureSheaf (op U))

/-- The objectwise sections functor admits an unbounded right derived functor. -/
instance moduleSectionsToDerived_hasRightDerivedFunctor (X : RingedSite.{u, v})
    [IsGrothendieckAbelian.{max u v} (Mod(X))] (U : X) :
    Functor.HasRightDerivedFunctor (moduleSectionsToDerived X U) (Qis(X)) := by
  sorry

/-- The unbounded right derived sections functor `R\Gamma(U,-)` on module sheaves. -/
noncomputable abbrev moduleSectionsDerived (X : RingedSite.{u, v}) (U : X)
    [IsGrothendieckAbelian.{max u v} (Mod(X))] :
    DMod(X) ⥤ DerivedCategory (_root_.ModuleCat (X.structureSheaf.1.obj (op U))) :=
  Functor.totalRightDerived (moduleSectionsToDerived X U)
    (DerivedCategory.Qh :
      HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X))
    (Qis(X))

end RingedSite.Hom

namespace RingedSiteDerivedSections

/- Lean surface notation for the unbounded derived global-sections functor `RΓ(X,-)` on a ringed
site. This is a scoped macro so the objectwise form `RΓ[X](U)` can share the same `RΓ` owner
surface without parser conflicts. -/
scoped macro:max "RΓ[" X:term "]" : term =>
  `(RingedSite.Hom.moduleGlobalSectionsDerived $X)

@[inherit_doc RingedSite.Hom.moduleSectionsDerived]
scoped notation3:max "RΓ[" X "](" U ")" =>
  RingedSite.Hom.moduleSectionsDerived X U

end RingedSiteDerivedSections
