import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_31_7
import StacksProject_2024.stacks_project.Chap19.Theorem_19_12_6
import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_3

open CategoryTheory
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

/-- The underived sections functor over a fixed object, viewed in abelian groups. -/
abbrev moduleSectionsAsAbelianFunctor (X : RingedSite.{u, v}) (U : X) :
    SheafOfModules X.structureSheaf ⥤ AddCommGrpCat.{max u v} :=
  underlyingAbelianSheafFunctor X ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

instance moduleSectionsAsAbelianFunctor_additive (X : RingedSite.{u, v}) (U : X)
    [Abelian (SheafOfModules X.structureSheaf)] :
    (moduleSectionsAsAbelianFunctor X U).Additive := by
  dsimp [moduleSectionsAsAbelianFunctor]
  infer_instance

instance moduleSectionsAsAbelianFunctor_preservesZeroMorphisms
    (X : RingedSite.{u, v}) (U : X) [Abelian (SheafOfModules X.structureSheaf)] :
    (moduleSectionsAsAbelianFunctor X U).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (moduleSectionsAsAbelianFunctor X U)

/-- The functor on homotopy categories induced by sections over a fixed object, viewed in
`D(\operatorname{Ab})`. -/
abbrev moduleSectionsAsAbelianToDerived (X : RingedSite.{u, v}) (U : X) :
    HomotopyCategory (SheafOfModules X.structureSheaf) (ComplexShape.up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  (moduleSectionsAsAbelianFunctor X U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

instance moduleSectionsAsAbelianToDerived_hasRightDerivedFunctor
    (X : RingedSite.{u, v}) [IsGrothendieckAbelian.{max u v} (SheafOfModules X.structureSheaf)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}] (U : X) :
    Functor.HasRightDerivedFunctor
      (moduleSectionsAsAbelianToDerived X U)
      (HomotopyCategory.quasiIso (SheafOfModules X.structureSheaf) (ComplexShape.up ℤ)) := by
  refine hasRightDerivedFunctor_of_kInjective_resolutions
      (moduleSectionsAsAbelianToDerived X U) ?_
  intro K
  obtain ⟨J, _, hKinj⟩ :=
    CochainComplex.exists_functorial_kInjective_resolution (SheafOfModules X.structureSheaf)
  exact ⟨J.toFunctor.obj K, hKinj K, J.ι.app K, J.quasiIso_app K⟩

/-- The derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in
`D(\operatorname{Ab})`. -/
abbrev moduleSectionsAsAbelianDerived (X : RingedSite.{u, v}) (U : X)
    [IsGrothendieckAbelian.{max u v} (SheafOfModules X.structureSheaf)] :
    DerivedCategory (SheafOfModules X.structureSheaf) ⥤ DerivedCategory AddCommGrpCat.{max u v} :=
  letI := moduleSectionsAsAbelianToDerived_hasRightDerivedFunctor X U
  Functor.totalRightDerived
    (moduleSectionsAsAbelianToDerived X U)
    (DerivedCategory.Qh :
      HomotopyCategory (SheafOfModules X.structureSheaf) (ComplexShape.up ℤ) ⥤
        DerivedCategory (SheafOfModules X.structureSheaf))
    (HomotopyCategory.quasiIso (SheafOfModules X.structureSheaf) (ComplexShape.up ℤ))

end RingedSite.Hom
