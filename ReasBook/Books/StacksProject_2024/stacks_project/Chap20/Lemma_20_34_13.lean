import StacksProject_2024.stacks_project.Chap20.Lemma_20_34_4
import StacksProject_2024.stacks_project.Chap20.Remark_20_34_12

open CategoryTheory
open AlgebraicGeometry
open ComplexShape
open scoped RingedSpace.Hom RingedSpaceClosedSubsetDerived
open scoped RingedSpaceClosedSubsetGlobalSectionsWithSupport

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

local notation "L(" f ")" "^*" => modulePullbackDerived f

/- Domain-style sampling for Lemma 20.34.13:
- primary domain: pullback on derived cohomology with support and its compatibility with the
  canonical forget-support maps;
- sampled owner declarations:
  `DerivedCategory.homologyFunctor`,
  `CategoryTheory.CommSq`,
  `CategoryTheory.derivedBaseChangeMap`,
  `closedSubsetPullback_sectionsWithSupportDerived_pushforward_commSq`;
- best owner abstraction:
  `source-facing`: the pullback map on cohomology with support and the resulting commutative
    square with the ordinary pullback map;
  `core/canonical`: `DerivedCategory.homologyFunctor`, `CategoryTheory.derivedBaseChangeMap`, and
    the derived closed-subset adjunctions `i⋆[hZ] ⊣ R𝓗[hZ]` and
    `i⋆[hZ'] ⊣ R𝓗[hZ']`;
  `bridge/view`: the ambient derived pullback square obtained by whiskering the owner comparison
    with the chosen pullback morphism on derived global sections.

Primitive data are the ambient pullback map on ordinary derived global sections together with the
canonical closed-subset derived base-change owner and the Chapter 20 identification
`RΓ_[hZ] ≅ R𝓗[hZ] ⋙ i⋆[hZ] ⋙ RΓ`. The source-facing pullback map on derived global
sections with support is obtained by transporting that bridge data across the canonical owner
isomorphisms, and the cohomology map is derived API obtained by applying degree-`n` homology. -/

section

variable {X X' : RingedSpace.{u}} {Z : Set X} {Z' : Set X'}
variable (f : X' ⟶ X) (hZ : IsClosed Z) (hZ' : IsClosed Z')
variable
  [CategoryWithHomology (RingedSpace.Modules X)]
  [CategoryWithHomology (RingedSpace.Modules X')]
  [(f^*).Additive]
  [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis X)]

private noncomputable abbrev derivedAdjunctionZ :
    i⋆[hZ] ⊣ R𝓗[hZ] :=
  closedSubsetModulePushforwardDerivedAdjunction X Z hZ

private noncomputable abbrev derivedAdjunctionZPrime :
    i⋆[hZ'] ⊣ R𝓗[hZ'] :=
  closedSubsetModulePushforwardDerivedAdjunction X' Z' hZ'

local notation "adjZ" => derivedAdjunctionZ hZ
local notation "adjZPrime" => derivedAdjunctionZPrime hZ'

variable
  (pullbackOnClosedSubsetDerived : closedSubsetModuleDerived X Z ⥤ closedSubsetModuleDerived X' Z')
  (derivedGlobalSections :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory AddCommGrpCat.{u})
  (derivedGlobalSectionsPrime :
    DerivedCategory (RingedSpace.Modules X') ⥤ DerivedCategory AddCommGrpCat.{u})
  (derivedGlobalSectionsPullback : derivedGlobalSections ⟶ L(f)^* ⋙ derivedGlobalSectionsPrime)
  (pullbackOnClosedSubsetPushforwardIso :
    pullbackOnClosedSubsetDerived ⋙ i⋆[hZ'] ≅ i⋆[hZ] ⋙ L(f)^*)

local notation "RΓ" => derivedGlobalSections

private abbrev forgetSupport :=
  (Functor.associator (R𝓗[hZ]) (i⋆[hZ]) RΓ).hom ≫
    Functor.whiskerRight
      (adjZ).counit
      RΓ

private abbrev forgetSupportPrime :=
  (Functor.associator (R𝓗[hZ']) (i⋆[hZ']) derivedGlobalSectionsPrime).hom ≫
    Functor.whiskerRight
      (adjZPrime).counit
      derivedGlobalSectionsPrime

private abbrev supportedAmbientPullback (K : DerivedCategory (RingedSpace.Modules X)) :=
  derivedGlobalSectionsPullback.app ((i⋆[hZ]).obj ((R𝓗[hZ]).obj K)) ≫
    derivedGlobalSectionsPrime.map
      (pullbackOnClosedSubsetPushforwardIso.inv.app ((R𝓗[hZ]).obj K) ≫
        (i⋆[hZ']).map
          (CategoryTheory.derivedBaseChangeMap (i⋆[hZ]) (i⋆[hZ'])
            pullbackOnClosedSubsetDerived (L(f)^*) (R𝓗[hZ]) (R𝓗[hZ'])
            (adjZ) (adjZPrime) pullbackOnClosedSubsetPushforwardIso K))

private theorem supportedAmbientPullback_commSq
    (K : DerivedCategory (RingedSpace.Modules X)) :
    CommSq
      (supportedAmbientPullback
        f
        hZ
        hZ'
        pullbackOnClosedSubsetDerived
        derivedGlobalSections
        derivedGlobalSectionsPrime
        derivedGlobalSectionsPullback
        pullbackOnClosedSubsetPushforwardIso
        K)
      ((forgetSupport
          hZ
          derivedGlobalSections
          ).app K)
      ((forgetSupportPrime
          hZ'
          derivedGlobalSectionsPrime
          ).app ((L(f)^*).obj K))
      (derivedGlobalSectionsPullback.app K) := by
  have hsupported :
      (pullbackOnClosedSubsetPushforwardIso.inv.app ((R𝓗[hZ]).obj K) ≫
          (i⋆[hZ']).map
            (CategoryTheory.derivedBaseChangeMap (i⋆[hZ]) (i⋆[hZ'])
              pullbackOnClosedSubsetDerived (L(f)^*) (R𝓗[hZ]) (R𝓗[hZ'])
              (adjZ) (adjZPrime) pullbackOnClosedSubsetPushforwardIso K)) ≫
        (adjZPrime).counit.app ((L(f)^*).obj K) =
      (L(f)^*).map ((adjZ).counit.app K) :=
    by
      simpa using
        (closedSubsetPullback_sectionsWithSupportDerived_pushforward_comp_counit
          f
          hZ
          hZ'
          pullbackOnClosedSubsetDerived
          pullbackOnClosedSubsetPushforwardIso
          K)
  have hnat :
      derivedGlobalSectionsPullback.app ((i⋆[hZ]).obj ((R𝓗[hZ]).obj K)) ≫
        derivedGlobalSectionsPrime.map ((L(f)^*).map ((adjZ).counit.app K)) =
      derivedGlobalSections.map ((adjZ).counit.app K) ≫
        derivedGlobalSectionsPullback.app K := by
    simpa [Functor.comp_map] using
      (derivedGlobalSectionsPullback.naturality ((adjZ).counit.app K)).symm
  have hsupportedMap :
      derivedGlobalSectionsPrime.map
          (pullbackOnClosedSubsetPushforwardIso.inv.app ((R𝓗[hZ]).obj K) ≫
            (i⋆[hZ']).map
              (CategoryTheory.derivedBaseChangeMap (i⋆[hZ]) (i⋆[hZ'])
                pullbackOnClosedSubsetDerived (L(f)^*) (R𝓗[hZ]) (R𝓗[hZ'])
                (adjZ) (adjZPrime) pullbackOnClosedSubsetPushforwardIso K)) ≫
        derivedGlobalSectionsPrime.map ((adjZPrime).counit.app ((L(f)^*).obj K)) =
      derivedGlobalSectionsPrime.map ((L(f)^*).map ((adjZ).counit.app K)) := by
    simpa [Functor.map_comp] using
      congrArg (fun t ↦ derivedGlobalSectionsPrime.map t) hsupported
  have hnat' :
      derivedGlobalSectionsPullback.app ((i⋆[hZ]).obj ((R𝓗[hZ]).obj K)) ≫
          derivedGlobalSectionsPrime.map
            (pullbackOnClosedSubsetPushforwardIso.inv.app ((R𝓗[hZ]).obj K) ≫
              (i⋆[hZ']).map
                (CategoryTheory.derivedBaseChangeMap (i⋆[hZ]) (i⋆[hZ'])
                  pullbackOnClosedSubsetDerived (L(f)^*) (R𝓗[hZ]) (R𝓗[hZ'])
                  (adjZ) (adjZPrime) pullbackOnClosedSubsetPushforwardIso K)) ≫
        derivedGlobalSectionsPrime.map ((adjZPrime).counit.app ((L(f)^*).obj K)) =
      derivedGlobalSections.map ((adjZ).counit.app K) ≫
        derivedGlobalSectionsPullback.app K := by
    calc
      _ =
          derivedGlobalSectionsPullback.app ((i⋆[hZ]).obj ((R𝓗[hZ]).obj K)) ≫
            derivedGlobalSectionsPrime.map ((L(f)^*).map ((adjZ).counit.app K)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun t ↦ derivedGlobalSectionsPullback.app ((i⋆[hZ]).obj ((R𝓗[hZ]).obj K)) ≫ t)
                  hsupportedMap
      _ = _ := hnat
  refine CommSq.mk ?_
  calc
    _ =
        derivedGlobalSectionsPullback.app ((i⋆[hZ]).obj ((R𝓗[hZ]).obj K)) ≫
          derivedGlobalSectionsPrime.map
            ((pullbackOnClosedSubsetPushforwardIso.inv.app ((R𝓗[hZ]).obj K) ≫
                (i⋆[hZ']).map
                  (CategoryTheory.derivedBaseChangeMap (i⋆[hZ]) (i⋆[hZ'])
                    pullbackOnClosedSubsetDerived (L(f)^*) (R𝓗[hZ]) (R𝓗[hZ'])
                    (adjZ) (adjZPrime) pullbackOnClosedSubsetPushforwardIso K)) ≫
              (adjZPrime).counit.app
                ((L(f)^*).obj K)) := by
          simp [forgetSupportPrime, Functor.map_comp, Category.assoc]
    _ =
        derivedGlobalSections.map
            ((adjZ).counit.app K) ≫
          derivedGlobalSectionsPullback.app K := by
            simpa [Functor.map_comp, Category.assoc] using hnat'
    _ = _ := by
          simp [forgetSupport]

-- Proof sketch: `forgetSupport` and `forgetSupport'` are the canonical cohomology maps of
-- Lemma `20.34.11`, while the top edge is obtained by applying degree-`n` homology to the
-- ambient pullback map followed by the canonical factorization from the generic derived
-- base-change owner specialized in Remark `20.34.12`. The
-- commutative-square theorem
-- `closedSubsetPullback_sectionsWithSupportDerived_pushforward_commSq` identifies the two composites
-- in the ambient derived category, and applying the homology functor gives the commutative square
-- below.
end

section

variable {X X' : RingedSpace.{u}} {Z : Set X} {Z' : Set X'}
variable (f : X' ⟶ X) (hZ : IsClosed Z) (hZ' : IsClosed Z')
variable
  [CategoryWithHomology (RingedSpace.Modules X)]
  [CategoryWithHomology (RingedSpace.Modules X')]
  [(f^*).Additive]
  [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis X)]

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
private noncomputable def closedSubsetPullback_sectionsWithSupportDerivedModel
    (derivedGlobalSectionsPullback :
      (moduleDerivedGlobalSections X ⋙
          (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory) ⟶
        L(f)^* ⋙
          (moduleDerivedGlobalSections X' ⋙
            (forget₂ (ModuleCat (globalSectionsRing X')) AddCommGrpCat.{u}).mapDerivedCategory))
    (pullbackOnClosedSubsetDerived :
      closedSubsetModuleDerived X Z ⥤ closedSubsetModuleDerived X' Z')
    (pullbackOnClosedSubsetPushforwardIso :
      pullbackOnClosedSubsetDerived ⋙ i⋆[hZ'] ≅ i⋆[hZ] ⋙ L(f)^*)
    (K : DModX) :
    ((RΓ_[hZ] ⋙
        (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory).obj K) ⟶
      ((L(f)^* ⋙ R𝓗[hZ'] ⋙ i⋆[hZ'] ⋙ moduleDerivedGlobalSections X' ⋙
          (forget₂ (ModuleCat (globalSectionsRing X')) AddCommGrpCat.{u}).mapDerivedCategory).obj
        K) :=
  (Functor.whiskerRight
      (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X Z hZ)
      (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory).app K ≫
    (supportedAmbientPullback
      f
      hZ
      hZ'
      pullbackOnClosedSubsetDerived
      (moduleDerivedGlobalSections X ⋙
        (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory)
      (moduleDerivedGlobalSections X' ⋙
        (forget₂ (ModuleCat (globalSectionsRing X')) AddCommGrpCat.{u}).mapDerivedCategory)
      derivedGlobalSectionsPullback
      pullbackOnClosedSubsetPushforwardIso
      K)

private theorem closedSubsetPullback_sectionsWithSupportDerived_model_commSq
    (derivedGlobalSectionsPullback :
      (moduleDerivedGlobalSections X ⋙
          (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory) ⟶
        L(f)^* ⋙
          (moduleDerivedGlobalSections X' ⋙
            (forget₂ (ModuleCat (globalSectionsRing X')) AddCommGrpCat.{u}).mapDerivedCategory))
    (pullbackOnClosedSubsetDerived :
      closedSubsetModuleDerived X Z ⥤ closedSubsetModuleDerived X' Z')
    (pullbackOnClosedSubsetPushforwardIso :
      pullbackOnClosedSubsetDerived ⋙ i⋆[hZ'] ≅ i⋆[hZ] ⋙ L(f)^*)
    (K : DModX) :
    CommSq
      (closedSubsetPullback_sectionsWithSupportDerivedModel
        f
        hZ
        hZ'
        derivedGlobalSectionsPullback
        pullbackOnClosedSubsetDerived
        pullbackOnClosedSubsetPushforwardIso
        K)
      ((Functor.whiskerRight
          (closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X Z hZ)
          (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory).app K)
      ((forget₂ (ModuleCat (globalSectionsRing X')) AddCommGrpCat.{u}).mapDerivedCategory.map
        ((moduleDerivedGlobalSections X').map
          ((closedSubsetModulePushforwardDerivedAdjunction X' Z' hZ').counit.app
            ((L(f)^*).obj K))))
      (derivedGlobalSectionsPullback.app K) := by
  let FX :
      DerivedCategory (ModuleCat (globalSectionsRing X)) ⥤
        DerivedCategory AddCommGrpCat.{u} :=
    (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory
  let FX' :
      DerivedCategory (ModuleCat (globalSectionsRing X')) ⥤
        DerivedCategory AddCommGrpCat.{u} :=
    (forget₂ (ModuleCat (globalSectionsRing X')) AddCommGrpCat.{u}).mapDerivedCategory
  let sq :=
    supportedAmbientPullback_commSq
      f
      hZ
      hZ'
      pullbackOnClosedSubsetDerived
      (moduleDerivedGlobalSections X ⋙ FX)
      (moduleDerivedGlobalSections X' ⋙ FX')
      derivedGlobalSectionsPullback
      pullbackOnClosedSubsetPushforwardIso
      K
  have hforget :
      ((Functor.whiskerRight
          (closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X Z hZ)
          FX).app K) =
        ((Functor.whiskerRight
            (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X Z hZ)
            FX).app K) ≫
          FX.map
            ((moduleDerivedGlobalSections X).map
              ((closedSubsetModulePushforwardDerivedAdjunction X Z hZ).counit.app K)) := by
    have happ :
        (closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X Z hZ).app K =
          (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X Z hZ).app K ≫
            (moduleDerivedGlobalSections X).map
              ((closedSubsetModulePushforwardDerivedAdjunction X Z hZ).counit.app K) := by
      change
        (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X Z hZ).app K ≫
              (Functor.associator (R𝓗[hZ]) (i⋆[hZ]) (moduleDerivedGlobalSections X)).hom.app K ≫
                (Functor.whiskerRight
                  (closedSubsetModulePushforwardDerivedAdjunction X Z hZ).counit
                  (moduleDerivedGlobalSections X)).app K =
          (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X Z hZ).app K ≫
            (moduleDerivedGlobalSections X).map
              ((closedSubsetModulePushforwardDerivedAdjunction X Z hZ).counit.app K)
      simp [Functor.whiskerRight_app]
    rw [Functor.whiskerRight_app, happ]
    exact
      FX.map_comp
        ((closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X Z hZ).app K)
        ((moduleDerivedGlobalSections X).map
          ((closedSubsetModulePushforwardDerivedAdjunction X Z hZ).counit.app K))
  refine CommSq.mk ?_
  calc
    closedSubsetPullback_sectionsWithSupportDerivedModel
        f
        hZ
        hZ'
        derivedGlobalSectionsPullback
        pullbackOnClosedSubsetDerived
        pullbackOnClosedSubsetPushforwardIso
        K ≫
      FX'.map
        ((moduleDerivedGlobalSections X').map
          ((closedSubsetModulePushforwardDerivedAdjunction X' Z' hZ').counit.app
            ((L(f)^*).obj K))) =
        ((Functor.whiskerRight
            (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X Z hZ)
            FX).app K) ≫
          supportedAmbientPullback
            f
            hZ
            hZ'
            pullbackOnClosedSubsetDerived
            (moduleDerivedGlobalSections X ⋙ FX)
            (moduleDerivedGlobalSections X' ⋙ FX')
            derivedGlobalSectionsPullback
            pullbackOnClosedSubsetPushforwardIso
            K ≫
          FX'.map
            ((moduleDerivedGlobalSections X').map
              ((closedSubsetModulePushforwardDerivedAdjunction X' Z' hZ').counit.app
                ((L(f)^*).obj K))) := by
          simp [closedSubsetPullback_sectionsWithSupportDerivedModel, FX, FX', Category.assoc]
    _ =
        ((Functor.whiskerRight
            (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X Z hZ)
            FX).app K) ≫
          FX.map
            ((moduleDerivedGlobalSections X).map
              ((closedSubsetModulePushforwardDerivedAdjunction X Z hZ).counit.app K)) ≫
          derivedGlobalSectionsPullback.app K := by
            simpa [FX, FX', Category.assoc] using congrArg
              (fun t ↦
                ((Functor.whiskerRight
                    (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X Z hZ)
                    FX).app K) ≫ t)
              sq.w
    _ =
        ((Functor.whiskerRight
            (closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X Z hZ)
            FX).app K) ≫
          derivedGlobalSectionsPullback.app K := by
            rw [hforget]
            simp [Category.assoc]

theorem closedSubsetPullback_sectionsWithSupportDerived_derived_commSq
    (derivedGlobalSectionsPullback :
      (moduleDerivedGlobalSections X ⋙
          (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory) ⟶
        L(f)^* ⋙
          (moduleDerivedGlobalSections X' ⋙
            (forget₂ (ModuleCat (globalSectionsRing X')) AddCommGrpCat.{u}).mapDerivedCategory))
    (pullbackOnClosedSubsetDerived :
      closedSubsetModuleDerived X Z ⥤ closedSubsetModuleDerived X' Z')
    (pullbackOnClosedSubsetPushforwardIso :
      pullbackOnClosedSubsetDerived ⋙ i⋆[hZ'] ≅ i⋆[hZ] ⋙ L(f)^*)
    (K : DModX)
    (supportedPullback :
      ((RΓ_[hZ] ⋙
          (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory).obj K) ⟶
        ((L(f)^* ⋙ RΓ_[hZ'] ⋙
            (forget₂ (ModuleCat (globalSectionsRing X')) AddCommGrpCat.{u}).mapDerivedCategory).obj
          K))
    (hsupportedPullback :
      supportedPullback ≫
          (Functor.whiskerLeft
              (L(f)^*)
              (Functor.whiskerRight
                (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X' Z' hZ')
                (forget₂
                  (ModuleCat (globalSectionsRing X'))
                  AddCommGrpCat.{u}).mapDerivedCategory)).app K =
        ((Functor.whiskerRight
            (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X Z hZ)
            (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory).app
          K) ≫
          derivedGlobalSectionsPullback.app ((i⋆[hZ]).obj ((R𝓗[hZ]).obj K)) ≫
          (moduleDerivedGlobalSections X' ⋙
              (forget₂ (ModuleCat (globalSectionsRing X')) AddCommGrpCat.{u}).mapDerivedCategory).map
            (pullbackOnClosedSubsetPushforwardIso.inv.app ((R𝓗[hZ]).obj K) ≫
              (i⋆[hZ']).map
                (CategoryTheory.derivedBaseChangeMap
                  (i⋆[hZ])
                  (i⋆[hZ'])
                  pullbackOnClosedSubsetDerived
                  (L(f)^*)
                  (R𝓗[hZ])
                  (R𝓗[hZ'])
                  (closedSubsetModulePushforwardDerivedAdjunction X Z hZ)
                  (closedSubsetModulePushforwardDerivedAdjunction X' Z' hZ')
                  pullbackOnClosedSubsetPushforwardIso
                  K))) :
    CommSq
      supportedPullback
      ((Functor.whiskerRight
          (closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X Z hZ)
          (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory).app K)
      ((Functor.whiskerRight
          (closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X' Z' hZ')
          (forget₂ (ModuleCat (globalSectionsRing X')) AddCommGrpCat.{u}).mapDerivedCategory).app
        ((L(f)^*).obj K))
      (derivedGlobalSectionsPullback.app K) := by
  let FX :
      DerivedCategory (ModuleCat (globalSectionsRing X)) ⥤
        DerivedCategory AddCommGrpCat.{u} :=
    (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory
  let FX' :
      DerivedCategory (ModuleCat (globalSectionsRing X')) ⥤
        DerivedCategory AddCommGrpCat.{u} :=
    (forget₂ (ModuleCat (globalSectionsRing X')) AddCommGrpCat.{u}).mapDerivedCategory
  have hsquare_model :=
    closedSubsetPullback_sectionsWithSupportDerived_model_commSq
      f
      hZ
      hZ'
      derivedGlobalSectionsPullback
      pullbackOnClosedSubsetDerived
      pullbackOnClosedSubsetPushforwardIso
      K
  refine CommSq.mk ?_
  have hstep₁ :
      supportedPullback ≫
          ((Functor.whiskerRight
              (closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X' Z' hZ')
              FX').app ((L(f)^*).obj K)) =
        supportedPullback ≫
          (Functor.whiskerLeft
              (L(f)^*)
              (Functor.whiskerRight
                (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X' Z' hZ')
                FX')).app K ≫
          FX'.map
            ((moduleDerivedGlobalSections X').map
              ((closedSubsetModulePushforwardDerivedAdjunction X' Z' hZ').counit.app
                ((L(f)^*).obj K))) := by
    have happ' :
        (closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X' Z' hZ').app
            ((L(f)^*).obj K) =
          (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X' Z' hZ').app
              ((L(f)^*).obj K) ≫
            (moduleDerivedGlobalSections X').map
              ((closedSubsetModulePushforwardDerivedAdjunction X' Z' hZ').counit.app
                ((L(f)^*).obj K)) := by
      change
        (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X' Z' hZ').app
              ((L(f)^*).obj K) ≫
            (Functor.associator (R𝓗[hZ']) (i⋆[hZ']) (moduleDerivedGlobalSections X')).hom.app
              ((L(f)^*).obj K) ≫
              (Functor.whiskerRight
                  (closedSubsetModulePushforwardDerivedAdjunction X' Z' hZ').counit
                  (moduleDerivedGlobalSections X')).app ((L(f)^*).obj K) =
          (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X' Z' hZ').app
              ((L(f)^*).obj K) ≫
            (moduleDerivedGlobalSections X').map
              ((closedSubsetModulePushforwardDerivedAdjunction X' Z' hZ').counit.app
                ((L(f)^*).obj K))
      simp [Functor.whiskerRight_app]
    rw [Functor.whiskerRight_app, happ', Functor.whiskerLeft_app, Functor.whiskerRight_app,
      ]
    exact congrArg
      (fun t ↦ supportedPullback ≫ t)
      (FX'.map_comp
        ((closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X' Z' hZ').app
          ((L(f)^*).obj K))
        ((moduleDerivedGlobalSections X').map
          ((closedSubsetModulePushforwardDerivedAdjunction X' Z' hZ').counit.app
            ((L(f)^*).obj K))))
  have hstep₂ :
      supportedPullback ≫
          (Functor.whiskerLeft
              (L(f)^*)
              (Functor.whiskerRight
                (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X' Z' hZ')
                FX')).app K ≫
          FX'.map
            ((moduleDerivedGlobalSections X').map
              ((closedSubsetModulePushforwardDerivedAdjunction X' Z' hZ').counit.app
                ((L(f)^*).obj K))) =
        closedSubsetPullback_sectionsWithSupportDerivedModel
          f
          hZ
          hZ'
          derivedGlobalSectionsPullback
          pullbackOnClosedSubsetDerived
          pullbackOnClosedSubsetPushforwardIso
          K ≫
        FX'.map
          ((moduleDerivedGlobalSections X').map
            ((closedSubsetModulePushforwardDerivedAdjunction X' Z' hZ').counit.app
              ((L(f)^*).obj K))) := by
    simpa
        [FX, FX', closedSubsetPullback_sectionsWithSupportDerivedModel, supportedAmbientPullback,
          Functor.comp_map, Functor.map_comp, Category.assoc] using
      congrArg
      (fun t ↦
        t ≫
          FX'.map
            ((moduleDerivedGlobalSections X').map
              ((closedSubsetModulePushforwardDerivedAdjunction X' Z' hZ').counit.app
                ((L(f)^*).obj K))))
      hsupportedPullback
  have hstep₃ :
      closedSubsetPullback_sectionsWithSupportDerivedModel
          f
          hZ
          hZ'
          derivedGlobalSectionsPullback
          pullbackOnClosedSubsetDerived
          pullbackOnClosedSubsetPushforwardIso
          K ≫
        FX'.map
          ((moduleDerivedGlobalSections X').map
            ((closedSubsetModulePushforwardDerivedAdjunction X' Z' hZ').counit.app
              ((L(f)^*).obj K))) =
        ((Functor.whiskerRight
            (closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X Z hZ)
            FX).app K) ≫
          derivedGlobalSectionsPullback.app K := by
    simpa [FX, FX'] using hsquare_model.w
  exact hstep₁.trans (hstep₂.trans hstep₃)

-- Proof sketch: the source-facing cohomology square follows from the comparison-form square above
-- as soon as the chosen supported pullback morphism factors through the canonical model-side
-- comparison. Applying degree-`n` homology preserves the commutative-square relation.
/-- Lemma 20.34.13: any pullback map on cohomology with support whose derived realization factors
through the canonical comparison of Lemma `20.34.4` commutes with the forget-support maps to
ordinary cohomology. -/
@[stacks 0G79]
theorem closedSubsetPullback_sectionsWithSupportDerived_cohomology_commSq
    (derivedGlobalSectionsPullback :
      (moduleDerivedGlobalSections X ⋙
          (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory) ⟶
        L(f)^* ⋙
          (moduleDerivedGlobalSections X' ⋙
            (forget₂ (ModuleCat (globalSectionsRing X')) AddCommGrpCat.{u}).mapDerivedCategory))
    (pullbackOnClosedSubsetDerived :
      closedSubsetModuleDerived X Z ⥤ closedSubsetModuleDerived X' Z')
    (pullbackOnClosedSubsetPushforwardIso :
      pullbackOnClosedSubsetDerived ⋙ i⋆[hZ'] ≅ i⋆[hZ] ⋙ L(f)^*)
    (K : DModX)
    (supportedPullback :
      ((RΓ_[hZ] ⋙
          (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory).obj K) ⟶
        ((L(f)^* ⋙ RΓ_[hZ'] ⋙
            (forget₂ (ModuleCat (globalSectionsRing X')) AddCommGrpCat.{u}).mapDerivedCategory).obj
          K))
    (hsupportedPullback :
      supportedPullback ≫
          (Functor.whiskerLeft
              (L(f)^*)
              (Functor.whiskerRight
                (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X' Z' hZ')
                (forget₂
                  (ModuleCat (globalSectionsRing X'))
                  AddCommGrpCat.{u}).mapDerivedCategory)).app K =
        ((Functor.whiskerRight
            (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X Z hZ)
            (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory).app
          K) ≫
          derivedGlobalSectionsPullback.app ((i⋆[hZ]).obj ((R𝓗[hZ]).obj K)) ≫
          (moduleDerivedGlobalSections X' ⋙
              (forget₂ (ModuleCat (globalSectionsRing X')) AddCommGrpCat.{u}).mapDerivedCategory).map
            (pullbackOnClosedSubsetPushforwardIso.inv.app ((R𝓗[hZ]).obj K) ≫
              (i⋆[hZ']).map
                (CategoryTheory.derivedBaseChangeMap
                  (i⋆[hZ])
                  (i⋆[hZ'])
                  pullbackOnClosedSubsetDerived
                  (L(f)^*)
                  (R𝓗[hZ])
                  (R𝓗[hZ'])
                  (closedSubsetModulePushforwardDerivedAdjunction X Z hZ)
                  (closedSubsetModulePushforwardDerivedAdjunction X' Z' hZ')
                  pullbackOnClosedSubsetPushforwardIso
                  K)))
    (n : ℤ) :
    CommSq
      ((DerivedCategory.homologyFunctor AddCommGrpCat n).map supportedPullback)
      ((DerivedCategory.homologyFunctor AddCommGrpCat n).map
        ((Functor.whiskerRight
            (closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X Z hZ)
            (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory).app
          K))
      ((DerivedCategory.homologyFunctor AddCommGrpCat n).map
        ((Functor.whiskerRight
            (closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X' Z' hZ')
            (forget₂ (ModuleCat (globalSectionsRing X')) AddCommGrpCat.{u}).mapDerivedCategory).app
          ((L(f)^*).obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat n).map
        (derivedGlobalSectionsPullback.app K)) := by
  let sq :=
    closedSubsetPullback_sectionsWithSupportDerived_derived_commSq
      f
      hZ
      hZ'
      derivedGlobalSectionsPullback
      pullbackOnClosedSubsetDerived
      pullbackOnClosedSubsetPushforwardIso
      K
      supportedPullback
      hsupportedPullback
  simpa using sq.map (DerivedCategory.homologyFunctor AddCommGrpCat n)

end

end AlgebraicGeometry.RingedSpace
