import StacksProject_2024.stacks_project.Chap18.Lemma_18_14_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_16
import StacksProject_2024.stacks_project.Chap13.Lemma_13_31_7
import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_5_core
import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_7_core

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite
open scoped RingedSiteDerived
open scoped RingedSiteDerivedSections

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 21.20.7:
- primary domain: derived comparison for forgetting `𝒪_X`-module structure to underlying
  abelian sheaves on a ringed site and then applying global sections, objectwise sections, or
  direct image;
- sampled owner declarations:
  `RingedSite.Hom.moduleGlobalSectionsDerived`,
  `RingedSite.Hom.moduleSectionsDerived`,
  `RingedSite.Hom.modulePushforwardDerived`,
  `CategoryTheory.GrothendieckTopology.comparisonTopologyPushforwardDerived`;
- best owner abstraction: this file is `bridge/view`; the module-side owners already live in
  `RΓ[X]`, `RΓ[X](U)`, and `R(f)_*`, while the forgetful bridges are the canonical owners
  `(underlyingAbelianSheafFunctor X).mapDerivedCategory` and
  `(forget₂ (_root_.ModuleCat (X.structureSheaf.1.obj (op U))) AddCommGrpCat).mapDerivedCategory`;
  on the abelian side, the target owners are the canonical total right derived functors of sheaf
  global sections, sheaf evaluation, and sheaf pushforward, rather than any extra file-local
  wrapper;
  direct image is the total right derived functor of the canonical sheaf pushforward
  `f.base.sheafPushforwardContinuous AddCommGrpCat Y.siteTopology X.siteTopology`;
- primitive data: the forgetful functor `SheafOfModules.toSheaf X.structureSheaf`, the module-side
  derived owners from Lemmas `21.19.1`, `21.20.5`, and `21.20.7_core`, together with the
  site-level abelian sheaf functors `Sheaf.Γ`, evaluation on sheaves,
  `sheafPushforwardContinuous`, and their standard derived constructions;
- derived API: theorem-level functor/objectwise `IsIsomorphic` companions for the three
  source-facing comparisons. The concrete comparison morphisms and their `IsIso` witnesses stay
  private implementation data because the current right-derived comparison route still carries
  proof-law provenance debt.

Source/core/bridge triage:
- `source-facing`: the three textbook comparison statements of Lemma `21.20.7`;
- `core/canonical`: `moduleGlobalSectionsDerived`, `moduleSectionsDerived`,
  `modulePushforwardDerived`, `SheafOfModules.toSheaf`, `Sheaf.Γ`,
  `sheafPushforwardContinuous`, and the Chapter 21 `mapHomotopyCategoryToDerived`-based total
  right derived owners;
- `bridge/view`: `underlyingAbelianSheafFunctor` from Lemma `21.20.3` together with the private
  comparison morphisms implementing the public theorem-level `IsIsomorphic` companions.

Primitive data versus derived API:
- primitive data: the underlying-abelian-sheaf forgetful functor and the imported module-side
  owners;
- derived API: theorem-level functor/objectwise `IsIsomorphic` companions for the three
  comparisons; the comparison morphisms themselves remain private implementation data. -/

section

variable (X : _root_.RingedSite.{u, v})

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)]
variable [IsGrothendieckAbelian.{max u v} (Sheaf X.siteTopology (AddCommGrpCat.{max u v}))]

private instance sheafToPresheaf_additive :
    (sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v}).Additive := by
  constructor
  intro F G f g
  ext U x
  rfl

private instance abelianPresheafLimit_additive :
    (lim : (X.carrierᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}).Additive := by
  constructor
  intro F G f g
  apply limit.hom_ext
  intro j
  change limMap (f + g) ≫ limit.π G j = (limMap f + limMap g) ≫ limit.π G j
  rw [limMap_π, Preadditive.add_comp, limMap_π, limMap_π]
  simp

private instance sheafGamma_additive :
    (Sheaf.Γ X.siteTopology AddCommGrpCat.{max u v}).Additive := by
  exact Functor.additive_of_iso
    (Sheaf.ΓNatIsoLim X.siteTopology AddCommGrpCat.{max u v}).symm

end

private abbrev abelianSheafHomotopyToDerived
    (X : _root_.RingedSite.{u, v}) :
    HomotopyCategory (Sheaf X.siteTopology AddCommGrpCat.{max u v}) (up ℤ) ⥤
      DerivedCategory (Sheaf X.siteTopology AddCommGrpCat.{max u v}) :=
  DerivedCategory.Qh

section

variable (X : _root_.RingedSite.{u, v})

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)]
variable [IsGrothendieckAbelian.{max u v} (Sheaf X.siteTopology (AddCommGrpCat.{max u v}))]

local notation "ModX" => ModuleCat X
local notation "DModX" => ModuleDerived X
local notation "QModX" =>
  (DerivedCategory.Qh : HomotopyCategory ModX (up ℤ) ⥤ DModX)

private abbrev abelianGlobalSectionsToDerived :
    HomotopyCategory (Sheaf X.siteTopology AddCommGrpCat.{max u v}) (up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  let F : Sheaf X.siteTopology AddCommGrpCat.{max u v} ⥤ AddCommGrpCat.{max u v} :=
    Sheaf.Γ X.siteTopology AddCommGrpCat.{max u v}
  let _ : F.Additive := sheafGamma_additive X
  mapHomotopyCategoryToDerived F

private instance abelianGlobalSectionsToDerived_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor (abelianGlobalSectionsToDerived X)
      (HomotopyCategory.quasiIso
        (Sheaf X.siteTopology AddCommGrpCat.{max u v})
        (up ℤ)) := by
  refine hasRightDerivedFunctor_of_kInjective_resolutions
      (abelianGlobalSectionsToDerived X) ?_
  intro K
  obtain ⟨J, _, hKinj⟩ := CochainComplex.exists_functorial_kInjective_resolution
    (Sheaf X.siteTopology AddCommGrpCat.{max u v})
  exact ⟨J.toFunctor.obj K, hKinj K, J.ι.app K, J.quasiIso_app K⟩

/-- The derived global-sections functor on abelian sheaves over the underlying site of a ringed
site. -/
abbrev abelianGlobalSectionsDerived
    (X : _root_.RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
    [IsGrothendieckAbelian.{max u v} (Sheaf X.siteTopology (AddCommGrpCat.{max u v}))] :
    DerivedCategory (Sheaf X.siteTopology AddCommGrpCat.{max u v}) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  Functor.totalRightDerived
    (abelianGlobalSectionsToDerived X)
    (DerivedCategory.Qh :
      HomotopyCategory (Sheaf X.siteTopology AddCommGrpCat.{max u v}) (up ℤ) ⥤
        DerivedCategory (Sheaf X.siteTopology AddCommGrpCat.{max u v}))
    (HomotopyCategory.quasiIso
      (Sheaf X.siteTopology AddCommGrpCat.{max u v})
      (up ℤ))

private noncomputable def moduleGlobalSectionsToDerived_underlyingAbelianCompIso :
    moduleGlobalSectionsToDerived X ≅
      (underlyingAbelianSheafFunctor X).mapHomotopyCategory (up ℤ) ⋙
        abelianGlobalSectionsToDerived X := by
  let forgetH := (underlyingAbelianSheafFunctor X).mapHomotopyCategory (up ℤ)
  let ΓH := (Sheaf.Γ X.siteTopology AddCommGrpCat.{max u v}).mapHomotopyCategory (up ℤ)
  simpa [moduleGlobalSectionsToDerived, moduleGlobalSectionsAdditiveFunctor,
      abelianGlobalSectionsToDerived, mapHomotopyCategoryToDerived, forgetH, ΓH] using
    Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso
          (underlyingAbelianSheafFunctor X)
          (Sheaf.Γ X.siteTopology AddCommGrpCat.{max u v}))
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{max u v} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{max u v}) ≪≫
      Functor.associator
        forgetH
        ΓH
        (DerivedCategory.Qh :
          HomotopyCategory AddCommGrpCat.{max u v} (up ℤ) ⥤
            DerivedCategory AddCommGrpCat.{max u v})

private noncomputable def moduleGlobalSectionsDerived_underlyingAbelianTargetNat :
    ((underlyingAbelianSheafFunctor X).mapHomotopyCategory (up ℤ) ⋙
        abelianGlobalSectionsToDerived X) ⟶
      QModX ⋙
        ((underlyingAbelianSheafFunctor X).mapDerivedCategory ⋙
          abelianGlobalSectionsDerived X) :=
  Functor.whiskerLeft
      ((underlyingAbelianSheafFunctor X).mapHomotopyCategory (up ℤ))
      (Functor.totalRightDerivedUnit
        (abelianGlobalSectionsToDerived X)
        (abelianSheafHomotopyToDerived X)
        (HomotopyCategory.quasiIso
          (Sheaf X.siteTopology AddCommGrpCat.{max u v})
          (up ℤ))) ≫
    (Functor.associator
      ((underlyingAbelianSheafFunctor X).mapHomotopyCategory (up ℤ))
      (abelianSheafHomotopyToDerived X)
      (abelianGlobalSectionsDerived X)).inv ≫
    Functor.whiskerRight
      ((underlyingAbelianSheafFunctor X).mapDerivedCategoryFactorsh.inv :
        (underlyingAbelianSheafFunctor X).mapHomotopyCategory (up ℤ) ⋙
            abelianSheafHomotopyToDerived X ⟶
          QModX ⋙ (underlyingAbelianSheafFunctor X).mapDerivedCategory)
      (abelianGlobalSectionsDerived X) ≫
    (Functor.associator
      QModX
      (underlyingAbelianSheafFunctor X).mapDerivedCategory
      (abelianGlobalSectionsDerived X)).hom

end

/-- Implementation comparison for Lemma 21.20.7 (1). -/
private noncomputable def moduleGlobalSectionsDerived_underlyingAbelianComparison
    (X : _root_.RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)]
    [IsGrothendieckAbelian.{max u v} (Sheaf X.siteTopology (AddCommGrpCat.{max u v}))] :
    RΓ[X] ⟶
      ((underlyingAbelianSheafFunctor X).mapDerivedCategory ⋙
        abelianGlobalSectionsDerived X) :=
  (RΓ[X]).rightDerivedDesc
    (Functor.totalRightDerivedUnit
      (moduleGlobalSectionsToDerived X)
      (DerivedCategory.Qh : HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
      (ModuleQis X))
    (ModuleQis X)
    ((underlyingAbelianSheafFunctor X).mapDerivedCategory ⋙
      abelianGlobalSectionsDerived X)
    ((moduleGlobalSectionsToDerived_underlyingAbelianCompIso X).hom ≫
      moduleGlobalSectionsDerived_underlyingAbelianTargetNat X)

/-- Implementation `IsIso` witness for Lemma 21.20.7 (1). -/
private instance moduleGlobalSectionsDerived_underlyingAbelianComparison_isIso
    (X : _root_.RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)]
    [IsGrothendieckAbelian.{max u v} (Sheaf X.siteTopology (AddCommGrpCat.{max u v}))] :
    IsIso (moduleGlobalSectionsDerived_underlyingAbelianComparison X) := by
  change IsIso
    (Functor.rightDerivedNatTrans
      (RΓ[X])
      ((underlyingAbelianSheafFunctor X).mapDerivedCategory ⋙
        abelianGlobalSectionsDerived X)
      (Functor.totalRightDerivedUnit
        (moduleGlobalSectionsToDerived X)
        (DerivedCategory.Qh : HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
        (ModuleQis X))
      (moduleGlobalSectionsDerived_underlyingAbelianTargetNat X)
      (ModuleQis X)
      (moduleGlobalSectionsToDerived_underlyingAbelianCompIso X).hom)
  sorry

/-- Lemma 21.20.7 (1), functor-level source-facing comparison. -/
@[stacks 0D6J]
theorem moduleGlobalSectionsDerived_underlyingAbelian_functor_isomorphic
    (X : _root_.RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)]
    [IsGrothendieckAbelian.{max u v} (Sheaf X.siteTopology (AddCommGrpCat.{max u v}))] :
    IsIsomorphic
      RΓ[X]
      ((underlyingAbelianSheafFunctor X).mapDerivedCategory ⋙
        abelianGlobalSectionsDerived X) := by
  let _ : IsIso (moduleGlobalSectionsDerived_underlyingAbelianComparison X) := by
    infer_instance
  exact ⟨asIso (moduleGlobalSectionsDerived_underlyingAbelianComparison X)⟩

/-- Lemma 21.20.7 (1), objectwise source-facing form. -/
@[stacks 0D6J]
theorem moduleGlobalSectionsDerived_underlyingAbelian_isomorphic
    (X : _root_.RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)]
    [IsGrothendieckAbelian.{max u v} (Sheaf X.siteTopology (AddCommGrpCat.{max u v}))]
    (K : ModuleDerived X) :
    IsIsomorphic
      ((RΓ[X]).obj K)
      (((underlyingAbelianSheafFunctor X).mapDerivedCategory ⋙
          abelianGlobalSectionsDerived X).obj K) := by
  let _ : IsIso ((moduleGlobalSectionsDerived_underlyingAbelianComparison X).app K) :=
    by infer_instance
  exact ⟨asIso ((moduleGlobalSectionsDerived_underlyingAbelianComparison X).app K)⟩

section

variable (X : _root_.RingedSite.{u, v})
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]

local notation "ModX" => ModuleCat X
local notation "DModX" => ModuleDerived X
local notation "QModX" =>
  (DerivedCategory.Qh : HomotopyCategory ModX (up ℤ) ⥤ DModX)

private noncomputable def moduleSectionsAsAbelianFunctor_forgetCompIso
    (U : X) :
    moduleSectionsAsAbelianFunctor X U ≅
      SheafOfModules.evaluation X.structureSheaf (op U) ⋙
        forget₂ (_root_.ModuleCat (X.structureSheaf.1.obj (op U)))
          AddCommGrpCat.{max u v} := by
  simpa [moduleSectionsAsAbelianFunctor, underlyingAbelianSheafFunctor] using
    (Functor.isoWhiskerRight
      (SheafOfModules.toSheafCompSheafToPresheafIso X.structureSheaf)
      ((evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)))

private noncomputable def moduleSectionsAsAbelianToDerived_forgetCompIso
    (U : X) :
    moduleSectionsAsAbelianToDerived X U ≅
      moduleSectionsToDerived X U ⋙
        (forget₂ (_root_.ModuleCat (X.structureSheaf.1.obj (op U)))
          AddCommGrpCat.{max u v}).mapDerivedCategory := by
  let evalAbH := (moduleSectionsAsAbelianFunctor X U).mapHomotopyCategory (up ℤ)
  let evalModH := (SheafOfModules.evaluation X.structureSheaf (op U)).mapHomotopyCategory (up ℤ)
  let forgetSec := forget₂ (_root_.ModuleCat (X.structureSheaf.1.obj (op U)))
    AddCommGrpCat.{max u v}
  let qModU :
      HomotopyCategory (_root_.ModuleCat (X.structureSheaf.1.obj (op U))) (up ℤ) ⥤
        DerivedCategory (_root_.ModuleCat (X.structureSheaf.1.obj (op U))) :=
    DerivedCategory.Qh
  let qAb :
      HomotopyCategory AddCommGrpCat.{max u v} (up ℤ) ⥤
        DerivedCategory AddCommGrpCat.{max u v} :=
    DerivedCategory.Qh
  let hEval :
      evalAbH ≅ evalModH ⋙ forgetSec.mapHomotopyCategory (up ℤ) :=
    (Functor.mapHomotopyCategoryIso
      (moduleSectionsAsAbelianFunctor_forgetCompIso X U)) ≪≫
      Functor.mapHomotopyCategoryCompIso
        (SheafOfModules.evaluation X.structureSheaf (op U))
        forgetSec
  simpa [moduleSectionsAsAbelianToDerived, moduleSectionsAsAbelianFunctor, moduleSectionsToDerived,
      mapHomotopyCategoryToDerived, evalAbH, evalModH, forgetSec, qModU, qAb] using
    Functor.isoWhiskerRight hEval qAb ≪≫
      (Functor.associator evalModH (forgetSec.mapHomotopyCategory (up ℤ)) qAb).symm ≪≫
      Functor.isoWhiskerLeft evalModH forgetSec.mapDerivedCategoryFactorsh.symm ≪≫
      (Functor.associator evalModH qModU forgetSec.mapDerivedCategory).symm

private noncomputable def moduleSectionsDerived_underlyingAbelianSourceUnit
    (U : X) :
    moduleSectionsToDerived X U ⋙
        (forget₂ (_root_.ModuleCat (X.structureSheaf.1.obj (op U)))
          AddCommGrpCat.{max u v}).mapDerivedCategory ⟶
      QModX ⋙
        (RΓ[X](U) ⋙
          (forget₂ (_root_.ModuleCat (X.structureSheaf.1.obj (op U)))
            AddCommGrpCat.{max u v}).mapDerivedCategory) :=
  Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (moduleSectionsToDerived X U)
        QModX
        (ModuleQis X))
      (forget₂ (_root_.ModuleCat (X.structureSheaf.1.obj (op U)))
        AddCommGrpCat.{max u v}).mapDerivedCategory ≫
    (Functor.associator
      QModX
      (RΓ[X](U))
      (forget₂ (_root_.ModuleCat (X.structureSheaf.1.obj (op U)))
        AddCommGrpCat.{max u v}).mapDerivedCategory).hom

private theorem moduleSectionsDerived_underlyingAbelian_isRightDerivedFunctor
    (U : X) :
    (RΓ[X](U) ⋙
      (forget₂ (_root_.ModuleCat (X.structureSheaf.1.obj (op U)))
        AddCommGrpCat.{max u v}).mapDerivedCategory).IsRightDerivedFunctor
      (moduleSectionsDerived_underlyingAbelianSourceUnit X U)
      (ModuleQis X) := by
  sorry

attribute [instance] moduleSectionsDerived_underlyingAbelian_isRightDerivedFunctor

end

/-- Implementation comparison for Lemma 21.20.7 (2). -/
private noncomputable def moduleSectionsDerived_underlyingAbelianComparison
    (X : _root_.RingedSite.{u, v})
    [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
    (U : X) :
    (RΓ[X](U) ⋙
        (forget₂ (_root_.ModuleCat (X.structureSheaf.1.obj (op U)))
          AddCommGrpCat.{max u v}).mapDerivedCategory) ⟶
      moduleSectionsAsAbelianDerived X U :=
  (RΓ[X](U) ⋙
      (forget₂ (_root_.ModuleCat (X.structureSheaf.1.obj (op U)))
        AddCommGrpCat.{max u v}).mapDerivedCategory).rightDerivedDesc
    (moduleSectionsDerived_underlyingAbelianSourceUnit X U)
    (ModuleQis X)
    (moduleSectionsAsAbelianDerived X U)
    ((moduleSectionsAsAbelianToDerived_forgetCompIso X U).inv ≫
      Functor.totalRightDerivedUnit
        (moduleSectionsAsAbelianToDerived X U)
        (DerivedCategory.Qh : HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
        (ModuleQis X))

/-- Implementation `IsIso` witness for Lemma 21.20.7 (2). -/
private instance moduleSectionsDerived_underlyingAbelianComparison_isIso
    (X : _root_.RingedSite.{u, v})
    [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
    (U : X) :
    IsIso (moduleSectionsDerived_underlyingAbelianComparison X U) := by
  change IsIso
    (Functor.rightDerivedNatTrans
      (RΓ[X](U) ⋙
        (forget₂ (_root_.ModuleCat (X.structureSheaf.1.obj (op U)))
          AddCommGrpCat.{max u v}).mapDerivedCategory)
      (moduleSectionsAsAbelianDerived X U)
      (moduleSectionsDerived_underlyingAbelianSourceUnit X U)
      (Functor.totalRightDerivedUnit
        (moduleSectionsAsAbelianToDerived X U)
        (DerivedCategory.Qh : HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
        (ModuleQis X))
      (ModuleQis X)
      (moduleSectionsAsAbelianToDerived_forgetCompIso X U).inv)
  sorry

/-- Lemma 21.20.7 (2), functor-level source-facing comparison. -/
@[stacks 0D6J]
theorem moduleSectionsDerived_underlyingAbelian_functor_isomorphic
    (X : _root_.RingedSite.{u, v})
    [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
    (U : X) :
    IsIsomorphic
      (RΓ[X](U) ⋙
        (forget₂ (_root_.ModuleCat (X.structureSheaf.1.obj (op U)))
          AddCommGrpCat.{max u v}).mapDerivedCategory)
      (moduleSectionsAsAbelianDerived X U) := by
  let _ : IsIso (moduleSectionsDerived_underlyingAbelianComparison X U) := by
    infer_instance
  exact ⟨asIso (moduleSectionsDerived_underlyingAbelianComparison X U)⟩

/-- Lemma 21.20.7 (2), objectwise source-facing form. -/
@[stacks 0D6J]
theorem moduleSectionsDerived_underlyingAbelian_isomorphic
    (X : _root_.RingedSite.{u, v})
    [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
    (U : X) (K : ModuleDerived X) :
    IsIsomorphic
      ((RΓ[X](U) ⋙
          (forget₂ (_root_.ModuleCat (X.structureSheaf.1.obj (op U)))
            AddCommGrpCat.{max u v}).mapDerivedCategory).obj K)
      ((moduleSectionsAsAbelianDerived X U).obj K) := by
  let _ : IsIso ((moduleSectionsDerived_underlyingAbelianComparison X U).app K) := by
    infer_instance
  exact ⟨asIso ((moduleSectionsDerived_underlyingAbelianComparison X U).app K)⟩

section

variable {X Y : _root_.RingedSite.{u, v}} (f : _root_.RingedSite.Hom X Y)

variable [f.modulePushforward.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [IsGrothendieckAbelian.{max u v}
  (Sheaf X.siteTopology (AddCommGrpCat.{max u v}))]

private instance sheafPushforwardContinuous_additive
    (f : _root_.RingedSite.Hom X Y) :
    (f.base.sheafPushforwardContinuous AddCommGrpCat.{max u v}
      Y.siteTopology X.siteTopology).Additive := by
  constructor
  intro F G α β
  ext U x
  rfl

end

section

variable {X Y : _root_.RingedSite.{u, v}} (f : _root_.RingedSite.Hom X Y)

variable [f.modulePushforward.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [IsGrothendieckAbelian.{max u v}
  (Sheaf X.siteTopology (AddCommGrpCat.{max u v}))]

local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y
local notation "DModX" => ModuleDerived X
local notation "QModX" =>
  (DerivedCategory.Qh : HomotopyCategory ModX (up ℤ) ⥤ DModX)

private abbrev abelianPushforwardToDerived :
    HomotopyCategory (Sheaf X.siteTopology AddCommGrpCat.{max u v}) (up ℤ) ⥤
      DerivedCategory (Sheaf Y.siteTopology AddCommGrpCat.{max u v}) :=
  let F : Sheaf X.siteTopology AddCommGrpCat.{max u v} ⥤
      Sheaf Y.siteTopology AddCommGrpCat.{max u v} :=
    f.base.sheafPushforwardContinuous AddCommGrpCat.{max u v}
      Y.siteTopology X.siteTopology
  let _ : F.Additive := sheafPushforwardContinuous_additive f
  mapHomotopyCategoryToDerived F

private instance abelianPushforwardToDerived_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor (abelianPushforwardToDerived f)
      (HomotopyCategory.quasiIso
        (Sheaf X.siteTopology AddCommGrpCat.{max u v})
        (up ℤ)) := by
  let F : Sheaf X.siteTopology AddCommGrpCat.{max u v} ⥤
      Sheaf Y.siteTopology AddCommGrpCat.{max u v} :=
    f.base.sheafPushforwardContinuous AddCommGrpCat.{max u v}
      Y.siteTopology X.siteTopology
  let _ : F.Additive := sheafPushforwardContinuous_additive f
  change Functor.HasRightDerivedFunctor (mapHomotopyCategoryToDerived F)
    (HomotopyCategory.quasiIso
      (Sheaf X.siteTopology AddCommGrpCat.{max u v})
      (up ℤ))
  refine hasRightDerivedFunctor_of_kInjective_resolutions
      (mapHomotopyCategoryToDerived F) ?_
  intro K
  obtain ⟨J, _, hKinj⟩ := CochainComplex.exists_functorial_kInjective_resolution
    (Sheaf X.siteTopology AddCommGrpCat.{max u v})
  exact ⟨J.toFunctor.obj K, hKinj K, J.ι.app K, J.quasiIso_app K⟩

/-- The derived pushforward functor on abelian sheaves induced by a morphism of ringed sites. -/
abbrev abelianPushforwardDerived
    (f : _root_.RingedSite.Hom X Y) :
    DerivedCategory (Sheaf X.siteTopology AddCommGrpCat.{max u v}) ⥤
      DerivedCategory (Sheaf Y.siteTopology AddCommGrpCat.{max u v}) :=
  Functor.totalRightDerived
    (abelianPushforwardToDerived f)
    (DerivedCategory.Qh :
      HomotopyCategory (Sheaf X.siteTopology AddCommGrpCat.{max u v}) (up ℤ) ⥤
        DerivedCategory (Sheaf X.siteTopology AddCommGrpCat.{max u v}))
    (HomotopyCategory.quasiIso
      (Sheaf X.siteTopology AddCommGrpCat.{max u v})
      (up ℤ))

private noncomputable def modulePushforwardToDerived_underlyingAbelianCompIso :
    modulePushforwardToDerived f ⋙ (underlyingAbelianSheafFunctor Y).mapDerivedCategory ≅
      (underlyingAbelianSheafFunctor X).mapHomotopyCategory (up ℤ) ⋙
        abelianPushforwardToDerived f := by
  let pushModH := (f.modulePushforward).mapHomotopyCategory (up ℤ)
  let forgetYH := (underlyingAbelianSheafFunctor Y).mapHomotopyCategory (up ℤ)
  let forgetXH := (underlyingAbelianSheafFunctor X).mapHomotopyCategory (up ℤ)
  let pushAbH :=
    (f.base.sheafPushforwardContinuous AddCommGrpCat.{max u v}
      Y.siteTopology X.siteTopology).mapHomotopyCategory (up ℤ)
  let hComp :
      pushModH ⋙ forgetYH ≅ forgetXH ⋙ pushAbH :=
    (Functor.mapHomotopyCategoryCompIso
        f.modulePushforward
        (underlyingAbelianSheafFunctor Y)).symm ≪≫
      (Functor.mapHomotopyCategoryIso
        (eqToIso
          (show
            f.modulePushforward ⋙ underlyingAbelianSheafFunctor Y =
              underlyingAbelianSheafFunctor X ⋙
                (f.base.sheafPushforwardContinuous AddCommGrpCat.{max u v}
                  Y.siteTopology X.siteTopology) by
            rfl))) ≪≫
      Functor.mapHomotopyCategoryCompIso
        (underlyingAbelianSheafFunctor X)
        (f.base.sheafPushforwardContinuous AddCommGrpCat.{max u v}
          Y.siteTopology X.siteTopology)
  simpa [modulePushforwardToDerived, abelianPushforwardToDerived, mapHomotopyCategoryToDerived,
      pushModH, forgetYH, forgetXH, pushAbH] using
    (Functor.associator pushModH
      (DerivedCategory.Qh :
        HomotopyCategory ModY (up ℤ) ⥤ DerivedCategory ModY)
      (underlyingAbelianSheafFunctor Y).mapDerivedCategory).symm ≪≫
      Functor.isoWhiskerLeft pushModH
        (underlyingAbelianSheafFunctor Y).mapDerivedCategoryFactorsh ≪≫
      Functor.associator
        pushModH
        forgetYH
        (abelianSheafHomotopyToDerived Y) ≪≫
      Functor.isoWhiskerRight hComp (abelianSheafHomotopyToDerived Y) ≪≫
      Functor.associator
        forgetXH
        pushAbH
        (abelianSheafHomotopyToDerived Y)

private noncomputable def modulePushforwardDerived_underlyingAbelianTargetNat :
    (underlyingAbelianSheafFunctor X).mapHomotopyCategory (up ℤ) ⋙
        abelianPushforwardToDerived f ⟶
      QModX ⋙
        ((underlyingAbelianSheafFunctor X).mapDerivedCategory ⋙
          abelianPushforwardDerived f) :=
  Functor.whiskerLeft
      ((underlyingAbelianSheafFunctor X).mapHomotopyCategory (up ℤ))
      (Functor.totalRightDerivedUnit
        (abelianPushforwardToDerived f)
        (abelianSheafHomotopyToDerived X)
        (HomotopyCategory.quasiIso
          (Sheaf X.siteTopology AddCommGrpCat.{max u v})
          (up ℤ))) ≫
    (Functor.associator
      ((underlyingAbelianSheafFunctor X).mapHomotopyCategory (up ℤ))
      (abelianSheafHomotopyToDerived X)
      (abelianPushforwardDerived f)).inv ≫
    Functor.whiskerRight
      ((underlyingAbelianSheafFunctor X).mapDerivedCategoryFactorsh.inv :
        (underlyingAbelianSheafFunctor X).mapHomotopyCategory (up ℤ) ⋙
            abelianSheafHomotopyToDerived X ⟶
          QModX ⋙ (underlyingAbelianSheafFunctor X).mapDerivedCategory)
      (abelianPushforwardDerived f) ≫
    (Functor.associator
      QModX
      (underlyingAbelianSheafFunctor X).mapDerivedCategory
      (abelianPushforwardDerived f)).hom

private noncomputable def modulePushforwardDerived_underlyingAbelianSourceUnit :
    modulePushforwardToDerived f ⋙ (underlyingAbelianSheafFunctor Y).mapDerivedCategory ⟶
      QModX ⋙
        (R(f)_* ⋙ (underlyingAbelianSheafFunctor Y).mapDerivedCategory) :=
  Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (modulePushforwardToDerived f)
        QModX
        (ModuleQis X))
      (underlyingAbelianSheafFunctor Y).mapDerivedCategory ≫
    (Functor.associator
      QModX
      (R(f)_*)
      (underlyingAbelianSheafFunctor Y).mapDerivedCategory).hom

private theorem modulePushforwardDerived_underlyingAbelian_isRightDerivedFunctor :
    ((R(f)_*) ⋙ (underlyingAbelianSheafFunctor Y).mapDerivedCategory).IsRightDerivedFunctor
      (modulePushforwardDerived_underlyingAbelianSourceUnit f)
      (ModuleQis X) := by
  sorry

attribute [instance] modulePushforwardDerived_underlyingAbelian_isRightDerivedFunctor

end

/-- Canonical right-adjoint comparison for Lemma 21.20.7 (3). -/
noncomputable def modulePushforwardDerived_underlyingAbelianComparison
    {X Y : _root_.RingedSite.{u, v}} (f : _root_.RingedSite.Hom X Y)
    [f.modulePushforward.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [IsGrothendieckAbelian.{max u v}
      (Sheaf X.siteTopology (AddCommGrpCat.{max u v}))] :
      (R(f)_* ⋙ (underlyingAbelianSheafFunctor Y).mapDerivedCategory) ⟶
      ((underlyingAbelianSheafFunctor X).mapDerivedCategory ⋙
        abelianPushforwardDerived f) :=
  ((R(f)_*) ⋙ (underlyingAbelianSheafFunctor Y).mapDerivedCategory).rightDerivedDesc
    (modulePushforwardDerived_underlyingAbelianSourceUnit f)
    (ModuleQis X)
    ((underlyingAbelianSheafFunctor X).mapDerivedCategory ⋙
      abelianPushforwardDerived f)
    ((modulePushforwardToDerived_underlyingAbelianCompIso f).hom ≫
      modulePushforwardDerived_underlyingAbelianTargetNat f)

/-- The canonical comparison for Lemma 21.20.7 (3) is an isomorphism. -/
instance modulePushforwardDerived_underlyingAbelianComparison_isIso
    {X Y : _root_.RingedSite.{u, v}} (f : _root_.RingedSite.Hom X Y)
    [f.modulePushforward.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [IsGrothendieckAbelian.{max u v}
      (Sheaf X.siteTopology (AddCommGrpCat.{max u v}))] :
    IsIso (modulePushforwardDerived_underlyingAbelianComparison f) := by
  change IsIso
    (Functor.rightDerivedNatTrans
      (R(f)_* ⋙ (underlyingAbelianSheafFunctor Y).mapDerivedCategory)
      ((underlyingAbelianSheafFunctor X).mapDerivedCategory ⋙
        abelianPushforwardDerived f)
      (modulePushforwardDerived_underlyingAbelianSourceUnit f)
      (modulePushforwardDerived_underlyingAbelianTargetNat f)
      (ModuleQis X)
      (modulePushforwardToDerived_underlyingAbelianCompIso f).hom)
  sorry

/-- Lemma 21.20.7 (3), functor-level source-facing comparison. -/
@[stacks 0D6J]
theorem modulePushforwardDerived_underlyingAbelian_functor_isomorphic
    {X Y : _root_.RingedSite.{u, v}} (f : _root_.RingedSite.Hom X Y)
    [f.modulePushforward.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [IsGrothendieckAbelian.{max u v}
      (Sheaf X.siteTopology (AddCommGrpCat.{max u v}))] :
    IsIsomorphic
      (R(f)_* ⋙ (underlyingAbelianSheafFunctor Y).mapDerivedCategory)
      ((underlyingAbelianSheafFunctor X).mapDerivedCategory ⋙
        abelianPushforwardDerived f) := by
  let _ : IsIso (modulePushforwardDerived_underlyingAbelianComparison f) := by
    infer_instance
  exact ⟨asIso (modulePushforwardDerived_underlyingAbelianComparison f)⟩

/-- Lemma 21.20.7 (3), objectwise source-facing form. -/
@[stacks 0D6J]
theorem modulePushforwardDerived_underlyingAbelian_isomorphic
    {X Y : _root_.RingedSite.{u, v}} (f : _root_.RingedSite.Hom X Y)
    [f.modulePushforward.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [IsGrothendieckAbelian.{max u v}
      (Sheaf X.siteTopology (AddCommGrpCat.{max u v}))]
    (K : ModuleDerived X) :
    IsIsomorphic
      (((R(f)_*) ⋙ (underlyingAbelianSheafFunctor Y).mapDerivedCategory).obj K)
      (((underlyingAbelianSheafFunctor X).mapDerivedCategory ⋙
          abelianPushforwardDerived f).obj K) := by
  let _ : IsIso ((modulePushforwardDerived_underlyingAbelianComparison f).app K) := by
    infer_instance
  exact ⟨asIso ((modulePushforwardDerived_underlyingAbelianComparison f).app K)⟩

end RingedSite.Hom
