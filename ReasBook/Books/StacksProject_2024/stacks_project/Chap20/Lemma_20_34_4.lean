import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_16
import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core
import StacksProject_2024.stacks_project.Chap20.Lemma_20_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

open scoped RingedSpaceClosedSubsetSectionsWithSupport
open scoped RingedSpaceClosedSubsetDerived

/- Domain-style sampling for Lemma 20.34.4:
- primary domain: total right derived functors of additive functors on categories of module
  sheaves on a ringed space, and the comparison between a derived functor of a composite and the
  composite of the chapter owners;
- sampled owner declarations:
  `globalSectionsRing`,
  `moduleGlobalSectionsFunctor`,
  `moduleDerivedGlobalSections`,
  `closedSubsetModuleSectionsWithSupportDerived`,
  `closedSubsetModulePushforwardDerived`;
- best owner abstraction: the chapter-level global-sections owner from `20_14_1_1`, the
  closed-subset derived owners from `20.34.1`. The present file is `bridge/view`: it compares the
  source-facing composite computing `Γ_Z(X, -)` with the existing composite of those owners,
  without keeping a lower-level exact-functor lift on the public theorem surface.

Source/core/bridge triage:
- `source-facing`: the underived functor computing `Γ_Z(X, -)` with values in
  `Γ(X, 𝒪_X)`-modules;
- `core/canonical`: `globalSectionsRing`, `moduleGlobalSectionsFunctor`,
  `moduleDerivedGlobalSections`, `closedSubsetModuleSectionsWithSupportDerived`, and
  `closedSubsetModulePushforwardDerived X Z hZ`;
- `bridge/view`: the comparison statement identifying the right derived functor of the source
  composite with the composite of those owners.

Primitive data are therefore just the closed-subset support functor and pushforward, plus the
existing chapter owner `moduleGlobalSectionsFunctor X`; the Grothendieck and derived global-
sections infrastructure is derived API and should be reused rather than redeclared locally.
-/

section

variable (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z)
local notation "ModX" => RingedSpace.Modules X
local notation "ModZ" => RingedSpace.closedSubsetModuleCategory X Z
local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DModZ" => closedSubsetModuleDerived X Z
local notation "DGlobalX" => DerivedCategory (ModuleCat (globalSectionsRing X))
local notation "QX" => (DerivedCategory.Q : CochainComplex ModX ℤ ⥤ DModX)
local notation "QZ" => (DerivedCategory.Q : CochainComplex ModZ ℤ ⥤ DModZ)
local notation "QGlobalX" =>
  (DerivedCategory.Q :
    CochainComplex (ModuleCat (globalSectionsRing X)) ℤ ⥤ DGlobalX)
local notation "QisX" => HomologicalComplex.quasiIso ModX (up ℤ)
local notation "QisZ" => HomologicalComplex.quasiIso ModZ (up ℤ)
local notation "pushforwardZ" => RingedSpace.closedSubsetModulePushforward X Z
local notation "derivedGlobalSectionsX" => moduleDerivedGlobalSections X

private abbrev closedSubsetModuleSectionsWithSupportPushforwardFunctor :
    ModX ⥤ ModX :=
  𝓗[hZ] ⋙ pushforwardZ

/-- The underived global-sections-with-support functor
`Γ_Z(X, -) = 𝓗_Z ⋙ i_* ⋙ Γ(X, -)`. -/
abbrev closedSubsetModuleGlobalSectionsWithSupportFunctor
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    RingedSpace.Modules X ⥤ ModuleCat (globalSectionsRing X) :=
  𝓗[hZ] ⋙
    RingedSpace.closedSubsetModulePushforward X Z ⋙
    moduleGlobalSectionsFunctor X

namespace ClosedSubsetGlobalSectionsWithSupport

/- Textbook surface notation for the global-sections-with-support functor `Γ_Z(X,-)`. The ambient
ringed space and subset are recovered from the closedness proof `hZ`. -/
@[inherit_doc AlgebraicGeometry.RingedSpace.closedSubsetModuleGlobalSectionsWithSupportFunctor]
scoped[RingedSpaceClosedSubsetGlobalSectionsWithSupport] notation:max "Γ_[" hZ "]" =>
  AlgebraicGeometry.RingedSpace.closedSubsetModuleGlobalSectionsWithSupportFunctor _ _ hZ

end ClosedSubsetGlobalSectionsWithSupport

open scoped RingedSpaceClosedSubsetGlobalSectionsWithSupport

private instance closedSubsetModuleSectionsWithSupportFunctor_hasRightDerivedFunctor :
    (Functor.mapHomologicalComplex (𝓗[hZ]) (up ℤ) ⋙ QZ).HasRightDerivedFunctor QisX :=
  mapHomologicalComplexQ_hasRightDerivedFunctor (𝓗[hZ])

private instance closedSubsetModuleSectionsWithSupportPushforwardFunctor_hasRightDerivedFunctor :
    (Functor.mapHomologicalComplex
        (closedSubsetModuleSectionsWithSupportPushforwardFunctor X Z hZ)
        (up ℤ) ⋙
      QX).HasRightDerivedFunctor QisX :=
  mapHomologicalComplexQ_hasRightDerivedFunctor
    (closedSubsetModuleSectionsWithSupportPushforwardFunctor X Z hZ)

private instance moduleGlobalSectionsFunctor_hasRightDerivedFunctor :
    (Functor.mapHomologicalComplex (moduleGlobalSectionsFunctor X) (up ℤ) ⋙
      QGlobalX).HasRightDerivedFunctor QisX :=
  mapHomologicalComplexQ_hasRightDerivedFunctor (moduleGlobalSectionsFunctor X)

private abbrev closedSubsetModulePushforwardToDerived :
    CochainComplex ModZ ℤ ⥤ DModX :=
  Functor.mapHomologicalComplex (RingedSpace.closedSubsetModulePushforward X Z) (up ℤ) ⋙
    QX

private theorem closedSubsetModulePushforwardToDerived_hasRightDerivedFunctor
    (hZ : IsClosed Z) :
    (closedSubsetModulePushforwardToDerived X Z).HasRightDerivedFunctor QisZ := by
  letI : PreservesFiniteLimits (RingedSpace.closedSubsetModulePushforward X Z) :=
    closedSubsetModulePushforward_preservesFiniteLimits X Z hZ
  letI : PreservesFiniteColimits (RingedSpace.closedSubsetModulePushforward X Z) :=
    closedSubsetModulePushforward_preservesFiniteColimits X Z hZ
  letI :
      ((RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategory).IsRightDerivedFunctor
        ((RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategoryFactors).inv
        QisZ :=
    Functor.isRightDerivedFunctor_of_inverts
      QisZ
      ((RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategory)
      ((RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategoryFactors)
  exact Functor.HasRightDerivedFunctor.mk'
    ((RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategory)
    ((RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategoryFactors).inv

private instance closedSubsetModuleGlobalSectionsWithSupportToDerived_hasRightDerivedFunctor :
    (Functor.mapHomologicalComplex Γ_[hZ] (up ℤ) ⋙ QGlobalX).HasRightDerivedFunctor QisX :=
  mapHomologicalComplexQ_hasRightDerivedFunctor Γ_[hZ]

/-- The derived global-sections-with-support functor `RΓ_Z(X, -)`. -/
abbrev closedSubsetModuleGlobalSectionsWithSupportDerived
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  let F :
      CochainComplex (RingedSpace.Modules X) ℤ ⥤
        DerivedCategory (ModuleCat (globalSectionsRing X)) :=
    Functor.mapHomologicalComplex Γ_[hZ] (up ℤ) ⋙
      (DerivedCategory.Q :
        CochainComplex (ModuleCat (globalSectionsRing X)) ℤ ⥤
          DerivedCategory (ModuleCat (globalSectionsRing X)))
  letI :
      F.HasRightDerivedFunctor
        (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ)) :=
    mapHomologicalComplexQ_hasRightDerivedFunctor Γ_[hZ]
  Functor.totalRightDerived
    F
    (DerivedCategory.Q :
      CochainComplex (RingedSpace.Modules X) ℤ ⥤
        DerivedCategory (RingedSpace.Modules X))
    (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))

namespace ClosedSubsetGlobalSectionsWithSupport

/- Textbook surface notation for the derived global-sections-with-support functor `RΓ_Z(X,-)`.
The ambient ringed space and subset are recovered from the closedness proof `hZ`. -/
@[inherit_doc AlgebraicGeometry.RingedSpace.closedSubsetModuleGlobalSectionsWithSupportDerived]
scoped[RingedSpaceClosedSubsetGlobalSectionsWithSupport] notation:max "RΓ_[" hZ "]" =>
  AlgebraicGeometry.RingedSpace.closedSubsetModuleGlobalSectionsWithSupportDerived _ _ hZ

end ClosedSubsetGlobalSectionsWithSupport

private abbrev closedSubsetModuleSectionsWithSupportPushforwardToDerived :
    CochainComplex ModX ℤ ⥤ DModX :=
  Functor.mapHomologicalComplex
      (closedSubsetModuleSectionsWithSupportPushforwardFunctor X Z hZ)
      (up ℤ) ⋙
    QX

private abbrev closedSubsetModuleSectionsWithSupportPushforwardDerived
    (hZ : IsClosed Z) :
    DModX ⥤ DModX :=
  letI :
      (closedSubsetModuleSectionsWithSupportPushforwardToDerived X Z hZ).HasRightDerivedFunctor
        QisX :=
    closedSubsetModuleSectionsWithSupportPushforwardFunctor_hasRightDerivedFunctor X Z hZ
  Functor.totalRightDerived
    (closedSubsetModuleSectionsWithSupportPushforwardToDerived X Z hZ)
    QX
    QisX

private noncomputable abbrev closedSubsetModulePushforwardDerivedTotal
    (hZ : IsClosed Z) :
    DModZ ⥤ DModX :=
  letI : (closedSubsetModulePushforwardToDerived X Z).HasRightDerivedFunctor QisZ :=
    closedSubsetModulePushforwardToDerived_hasRightDerivedFunctor X Z hZ
  Functor.totalRightDerived (closedSubsetModulePushforwardToDerived X Z) QZ QisZ

private noncomputable abbrev closedSubsetModulePushforwardDerivedTotalIso :
    closedSubsetModulePushforwardDerivedTotal X Z hZ ≅
      i⋆[hZ] :=
  letI : (closedSubsetModulePushforwardToDerived X Z).HasRightDerivedFunctor QisZ :=
    closedSubsetModulePushforwardToDerived_hasRightDerivedFunctor X Z hZ
  letI : PreservesFiniteLimits (RingedSpace.closedSubsetModulePushforward X Z) :=
    closedSubsetModulePushforward_preservesFiniteLimits X Z hZ
  letI : PreservesFiniteColimits (RingedSpace.closedSubsetModulePushforward X Z) :=
    closedSubsetModulePushforward_preservesFiniteColimits X Z hZ
  letI :
      ((RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategory).IsRightDerivedFunctor
        ((RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategoryFactors).inv
        QisZ :=
    Functor.isRightDerivedFunctor_of_inverts
      QisZ
      ((RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategory)
      ((RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategoryFactors)
  (closedSubsetModulePushforwardDerivedTotal X Z hZ).rightDerivedUnique
    ((RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategory)
    (Functor.totalRightDerivedUnit (closedSubsetModulePushforwardToDerived X Z) QZ QisZ)
    ((RingedSpace.closedSubsetModulePushforward X Z).mapDerivedCategoryFactors).inv
    QisZ

private instance closedSubsetModuleSectionsWithSupportPushforwardToDerived_hasRightDerivedFunctor :
    ((Functor.mapHomologicalComplex (𝓗[hZ]) (up ℤ)) ⋙
      closedSubsetModulePushforwardToDerived X Z).HasRightDerivedFunctor QisX := by
  change
    ((Functor.mapHomologicalComplex
        (closedSubsetModuleSectionsWithSupportPushforwardFunctor X Z hZ)
        (up ℤ)) ⋙
      QX).HasRightDerivedFunctor QisX
  simpa using
    closedSubsetModuleSectionsWithSupportPushforwardFunctor_hasRightDerivedFunctor X Z hZ

private noncomputable def closedSubsetModuleSectionsWithSupportPushforwardDerivedComparison :
    closedSubsetModuleSectionsWithSupportPushforwardDerived X Z hZ ⟶
      R𝓗[hZ] ⋙ closedSubsetModulePushforwardDerivedTotal X Z hZ :=
  let instF :
      ((Functor.mapHomologicalComplex (𝓗[hZ]) (up ℤ)) ⋙ QZ).HasRightDerivedFunctor QisX :=
    closedSubsetModuleSectionsWithSupportFunctor_hasRightDerivedFunctor X Z hZ
  let instComp :
      ((Functor.mapHomologicalComplex (𝓗[hZ]) (up ℤ)) ⋙
        closedSubsetModulePushforwardToDerived X Z).HasRightDerivedFunctor QisX :=
    inferInstance
  let instG :
      (closedSubsetModulePushforwardToDerived X Z).HasRightDerivedFunctor QisZ :=
    closedSubsetModulePushforwardToDerived_hasRightDerivedFunctor X Z hZ
  @Functor.rightDerivedCompComparison
    _ _ _ _ _ _
    QisX
    QisZ
    (Functor.mapHomologicalComplex (𝓗[hZ]) (up ℤ))
    (closedSubsetModulePushforwardToDerived X Z)
    instComp
    instF
    instG

private instance
    closedSubsetModuleGlobalSectionsWithSupportCompositeToDerived_hasRightDerivedFunctor :
    ((Functor.mapHomologicalComplex
        (closedSubsetModuleSectionsWithSupportPushforwardFunctor X Z hZ)
        (up ℤ)) ⋙
      Functor.mapHomologicalComplex (moduleGlobalSectionsFunctor X) (up ℤ) ⋙
        QGlobalX).HasRightDerivedFunctor QisX := by
  change
    ((Functor.mapHomologicalComplex
        (closedSubsetModuleGlobalSectionsWithSupportFunctor X Z hZ)
        (up ℤ)) ⋙
      QGlobalX).HasRightDerivedFunctor QisX
  simpa using
    closedSubsetModuleGlobalSectionsWithSupportToDerived_hasRightDerivedFunctor X Z hZ

private noncomputable def closedSubsetModuleGlobalSectionsWithSupportDerivedCompositeComparison :
    RΓ_[hZ] ⟶
      (closedSubsetModuleSectionsWithSupportPushforwardDerived X Z hZ ⋙
        moduleDerivedGlobalSections X) :=
  let instF :
      ((Functor.mapHomologicalComplex
          (closedSubsetModuleSectionsWithSupportPushforwardFunctor X Z hZ)
          (up ℤ)) ⋙
        QX).HasRightDerivedFunctor QisX :=
    closedSubsetModuleSectionsWithSupportPushforwardFunctor_hasRightDerivedFunctor X Z hZ
  let instG :
      (Functor.mapHomologicalComplex (moduleGlobalSectionsFunctor X) (up ℤ) ⋙
        QGlobalX).HasRightDerivedFunctor QisX :=
    moduleGlobalSectionsFunctor_hasRightDerivedFunctor X
  let instComp :
      ((Functor.mapHomologicalComplex
          (closedSubsetModuleSectionsWithSupportPushforwardFunctor X Z hZ)
          (up ℤ)) ⋙
        (Functor.mapHomologicalComplex (moduleGlobalSectionsFunctor X) (up ℤ) ⋙
          QGlobalX)).HasRightDerivedFunctor QisX :=
    closedSubsetModuleGlobalSectionsWithSupportCompositeToDerived_hasRightDerivedFunctor X Z hZ
  @Functor.rightDerivedCompComparison
    _ _ _ _ _ _
    QisX
    QisX
    (Functor.mapHomologicalComplex
      (closedSubsetModuleSectionsWithSupportPushforwardFunctor X Z hZ)
      (up ℤ))
    (Functor.mapHomologicalComplex (moduleGlobalSectionsFunctor X) (up ℤ) ⋙
      QGlobalX)
    instComp
    instF
    instG

/-- Lemma 20.34.4: for a ringed space `(X, 𝒪_X)` and the inclusion of a closed subset
`i : Z ⟶ X`, the composite `R𝓗_Z ⋙ Ri_* ⋙ RΓ(X, -)` is canonically isomorphic to
`RΓ_Z(X, -)`. In this file the codomain `D(Γ(X, 𝒪_X))` is modeled by first pushing the supported
sheaf on `Z` forward to `X` and then applying `RΓ(X, -)`. -/
@[stacks 0G70]
noncomputable def closedSubsetModuleGlobalSectionsWithSupportDerivedComparison :
    RΓ_[hZ] ⟶ R𝓗[hZ] ⋙ i⋆[hZ] ⋙ derivedGlobalSectionsX :=
  let step₁ :
      RΓ_[hZ] ⟶
        closedSubsetModuleSectionsWithSupportPushforwardDerived X Z hZ ⋙ derivedGlobalSectionsX :=
    closedSubsetModuleGlobalSectionsWithSupportDerivedCompositeComparison X Z hZ
  let step₂ :
      closedSubsetModuleSectionsWithSupportPushforwardDerived X Z hZ ⋙ derivedGlobalSectionsX ⟶
        (R𝓗[hZ] ⋙ closedSubsetModulePushforwardDerivedTotal X Z hZ) ⋙ derivedGlobalSectionsX :=
    Functor.whiskerRight
      (closedSubsetModuleSectionsWithSupportPushforwardDerivedComparison X Z hZ)
      derivedGlobalSectionsX
  let step₃ :
      (R𝓗[hZ] ⋙ closedSubsetModulePushforwardDerivedTotal X Z hZ) ⋙ derivedGlobalSectionsX ⟶
        R𝓗[hZ] ⋙ (closedSubsetModulePushforwardDerivedTotal X Z hZ ⋙ derivedGlobalSectionsX) :=
    (Functor.associator
      (R𝓗[hZ])
      (closedSubsetModulePushforwardDerivedTotal X Z hZ)
      derivedGlobalSectionsX).hom
  let step₄ :
      R𝓗[hZ] ⋙ (closedSubsetModulePushforwardDerivedTotal X Z hZ ⋙ derivedGlobalSectionsX) ⟶
        R𝓗[hZ] ⋙ i⋆[hZ] ⋙ derivedGlobalSectionsX :=
    Functor.whiskerLeft
      (R𝓗[hZ])
      (Functor.isoWhiskerRight
        (closedSubsetModulePushforwardDerivedTotalIso X Z hZ)
        derivedGlobalSectionsX).hom
  step₁ ≫ step₂ ≫ step₃ ≫ step₄

/-- The canonical forget-support morphism
`RΓ_Z(X, -) ⟶ RΓ(X, -)` induced by the comparison of Lemma 20.34.4 and the counit of
`i⋆[hZ] ⊣ R𝓗[hZ]`. -/
noncomputable def closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport :
    RΓ_[hZ] ⟶ derivedGlobalSectionsX :=
  closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X Z hZ ≫
    (Functor.associator (R𝓗[hZ]) (i⋆[hZ]) derivedGlobalSectionsX).hom ≫
    Functor.whiskerRight
      (closedSubsetModulePushforwardDerivedAdjunction X Z hZ).counit
      derivedGlobalSectionsX

/-- Lemma 20.34.4: for a ringed space `(X, 𝒪_X)` and the inclusion of a closed subset
`i : Z ⟶ X`, the canonical comparison morphism
`RΓ_Z(X, -) ⟶ R𝓗_Z ⋙ Ri_* ⋙ RΓ(X, -)` is an isomorphism. -/
@[stacks 0G70]
instance closedSubsetModuleGlobalSectionsWithSupportDerivedComparison_isIso :
    IsIso (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X Z hZ) := by
  sorry

/-- Objectwise companion to Lemma 20.34.4: the canonical comparison on any derived module is an
isomorphism. -/
theorem closedSubsetModuleGlobalSectionsWithSupportDerivedComparison_app_isIso
    (K : DModX) :
    IsIso ((closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X Z hZ).app K) := by
  infer_instance

end

end AlgebraicGeometry.RingedSpace
