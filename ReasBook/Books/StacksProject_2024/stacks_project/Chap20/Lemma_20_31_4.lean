import StacksProject_2024.stacks_project.Chap20.Lemma_20_25_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_33_1

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {ι : Type u}

local notation "ΓModX" => ModuleCat (globalSectionsRing X)
local notation "KplusMod" => CochainComplex.Plus (RingedSpace.Modules X)
local notation "DplusModX" => boundedBelowDerivedCategory (RingedSpace.Modules X)
local notation "DplusΓX" => boundedBelowDerivedCategory ΓModX

/- Domain-style sampling for Lemma 20.31.4:
- primary domain: the bounded-below Čech/global-sections tensor square on a ringed space;
- sampled owner declarations:
  `moduleCechDerivedFunctor`,
  `IsModuleCechToDerivedGlobalSectionsComparison`,
  `exists_moduleCechToDerivedGlobalSections`,
  `relativeDerivedCupProduct`,
  `derivedPushforward_tensor_naiveCupProduct_commSq`;
- source/core/bridge triage:
  `source-facing`: the bounded-below Čech/global-sections specialization for a comparison
    `τ : CechF ⟶ KplusToDplusModX ⋙ RΓplus`;
  `core/canonical`: `derivedPushforward_tensor_naiveCupProduct_commSq`;
  `bridge/view`: the specialization below from the categorical owner to the Chapter 20 Čech/global-
    sections comparison of Lemma `20.25.1`.

Primitive data are the Čech comparison morphism `τ`, the bounded-below tensor representatives on
the Čech and source sides, and the pullback-side compatibility square. The commuting tensor square
itself is already owned by Chapter 21, so this file keeps only the Chapter 20 specialization and
the corollary choosing `τ` from Lemma `20.25.1`. -/

variable (𝒰 : ι → Opens X.carrier)

local notation "QplusModX" =>
  mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 (RingedSpace.Modules X))
local notation "KplusToDplusModX" =>
  HomotopyCategory.Plus.quotient (RingedSpace.Modules X) ⋙ QplusModX
local notation "RΓplus" => boundedBelowDerivedGlobalSections X
local notation "CechF" => moduleCechDerivedFunctor X 𝒰

/-- For any Čech/global-sections comparison `τ` satisfying the compatibility hypothesis of
Lemma `20.25.1`, the specialized tensor/naive-cup-product square of Lemma `20.31.4` commutes. -/
theorem moduleCechToDerivedGlobalSections_tensor_naiveCupProduct_commSq
    [EnoughInjectives (RingedSpace.Modules X)]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (moduleGlobalSectionsFunctor X))
      (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    (leftDerivedPullback : DplusΓX ⥤ DplusModX)
    (globalSectionsAdj : leftDerivedPullback ⊣ RΓplus)
    (derivedTensorX : DplusModX ⥤ DplusModX ⥤ DplusModX)
    (derivedTensorΓ : DplusΓX ⥤ DplusΓX ⥤ DplusΓX)
    (pullbackTensorIso :
      ∀ A B : DplusΓX,
        leftDerivedPullback.obj ((derivedTensorΓ.obj B).obj A) ≅
          ((derivedTensorX.obj (leftDerivedPullback.obj B)).obj
            (leftDerivedPullback.obj A)))
    (sourceTensorComplex : KplusMod → KplusMod → KplusMod)
    (cechTensorComplex : KplusMod → KplusMod → DplusΓX)
    (cechTensorCounit :
      ∀ K M : KplusMod,
        ((derivedTensorΓ.obj ((CechF).obj M)).obj
          ((CechF).obj K)) ⟶
          cechTensorComplex K M)
    (naiveCupProduct :
      ∀ K M : KplusMod,
        cechTensorComplex K M ⟶ (CechF).obj (sourceTensorComplex K M))
    (sourceTensorCounit :
      ∀ K M : KplusMod, ((derivedTensorX.obj ((KplusToDplusModX).obj M)).obj
          ((KplusToDplusModX).obj K)) ⟶
            (KplusToDplusModX).obj (sourceTensorComplex K M))
    (pullbackCompatibility :
      ∀ (τ : CechF ⟶ KplusToDplusModX ⋙ RΓplus) (K M : KplusMod),
        IsModuleCechToDerivedGlobalSectionsComparison X 𝒰 τ →
        CommSq
          (leftDerivedPullback.map
            (((derivedTensorΓ.map (τ.app M)).app ((CechF).obj K)) ≫
              ((derivedTensorΓ.obj ((RΓplus).obj ((KplusToDplusModX).obj M))).map
                (τ.app K))))
          (leftDerivedPullback.map (cechTensorCounit K M ≫ naiveCupProduct K M))
          (relativeDerivedCupProductAdjointMap
              leftDerivedPullback
              RΓplus
              globalSectionsAdj
              derivedTensorX
              derivedTensorΓ
              pullbackTensorIso
              ((KplusToDplusModX).obj K)
              ((KplusToDplusModX).obj M) ≫
            sourceTensorCounit K M)
          ((globalSectionsAdj.homEquiv
              ((CechF).obj (sourceTensorComplex K M))
              ((KplusToDplusModX).obj (sourceTensorComplex K M))).symm
            (τ.app (sourceTensorComplex K M))))
    (τ : CechF ⟶ KplusToDplusModX ⋙ RΓplus)
    (hτ : IsModuleCechToDerivedGlobalSectionsComparison X 𝒰 τ)
    (K M : KplusMod) :
    CommSq
      (((derivedTensorΓ.map (τ.app M)).app ((CechF).obj K)) ≫
        ((derivedTensorΓ.obj ((RΓplus).obj ((KplusToDplusModX).obj M))).map
          (τ.app K)))
      (cechTensorCounit K M ≫ naiveCupProduct K M)
      (relativeDerivedCupProduct
          leftDerivedPullback
          RΓplus
          globalSectionsAdj
          derivedTensorX
          derivedTensorΓ
          pullbackTensorIso
          ((KplusToDplusModX).obj K)
          ((KplusToDplusModX).obj M) ≫
        (RΓplus).map (sourceTensorCounit K M))
      (τ.app (sourceTensorComplex K M)) := by
  simpa using
    (derivedPushforward_tensor_naiveCupProduct_commSq
      leftDerivedPullback
      RΓplus
      globalSectionsAdj
      derivedTensorX
      derivedTensorΓ
      pullbackTensorIso
      (KplusToDplusModX).obj
      id
      (CechF).obj
      sourceTensorComplex
      cechTensorComplex
      cechTensorCounit
      τ.app
      naiveCupProduct
      sourceTensorCounit
      (fun K ↦
        (globalSectionsAdj.homEquiv ((CechF).obj K) ((KplusToDplusModX).obj K)).symm
          (τ.app K))
      (fun K ↦ rfl)
      (fun K M ↦ pullbackCompatibility τ K M hτ)
      K
      M)

/-- Choosing a Čech/global-sections comparison from Lemma `20.25.1`, the specialized tensor/
naive-cup-product square of Lemma `20.31.4` holds for that comparison. -/
theorem exists_moduleCechToDerivedGlobalSections_tensor_naiveCupProduct_commSq
    [EnoughInjectives (RingedSpace.Modules X)]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (moduleGlobalSectionsFunctor X))
      (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    (h𝒰 : iSup 𝒰 = ⊤)
    (leftDerivedPullback : DplusΓX ⥤ DplusModX)
    (globalSectionsAdj : leftDerivedPullback ⊣ RΓplus)
    (derivedTensorX : DplusModX ⥤ DplusModX ⥤ DplusModX)
    (derivedTensorΓ : DplusΓX ⥤ DplusΓX ⥤ DplusΓX)
    (pullbackTensorIso :
      ∀ A B : DplusΓX,
        leftDerivedPullback.obj ((derivedTensorΓ.obj B).obj A) ≅
          ((derivedTensorX.obj (leftDerivedPullback.obj B)).obj
            (leftDerivedPullback.obj A)))
    (sourceTensorComplex : KplusMod → KplusMod → KplusMod)
    (cechTensorComplex : KplusMod → KplusMod → DplusΓX)
    (cechTensorCounit :
      ∀ K M : KplusMod,
        ((derivedTensorΓ.obj ((CechF).obj M)).obj
          ((CechF).obj K)) ⟶
          cechTensorComplex K M)
    (naiveCupProduct :
      ∀ K M : KplusMod,
        cechTensorComplex K M ⟶ (CechF).obj (sourceTensorComplex K M))
    (sourceTensorCounit :
      ∀ K M : KplusMod, ((derivedTensorX.obj ((KplusToDplusModX).obj M)).obj
          ((KplusToDplusModX).obj K)) ⟶
            (KplusToDplusModX).obj (sourceTensorComplex K M))
    (pullbackCompatibility :
      ∀ (τ : CechF ⟶ KplusToDplusModX ⋙ RΓplus) (K M : KplusMod),
        IsModuleCechToDerivedGlobalSectionsComparison X 𝒰 τ →
        CommSq
          (leftDerivedPullback.map
            (((derivedTensorΓ.map (τ.app M)).app ((CechF).obj K)) ≫
              ((derivedTensorΓ.obj ((RΓplus).obj ((KplusToDplusModX).obj M))).map
                (τ.app K))))
          (leftDerivedPullback.map (cechTensorCounit K M ≫ naiveCupProduct K M))
          (relativeDerivedCupProductAdjointMap
              leftDerivedPullback
              RΓplus
              globalSectionsAdj
              derivedTensorX
              derivedTensorΓ
              pullbackTensorIso
              ((KplusToDplusModX).obj K)
              ((KplusToDplusModX).obj M) ≫
            sourceTensorCounit K M)
          ((globalSectionsAdj.homEquiv
              ((CechF).obj (sourceTensorComplex K M))
              ((KplusToDplusModX).obj (sourceTensorComplex K M))).symm
            (τ.app (sourceTensorComplex K M))))
    (K M : KplusMod) :
    ∃ τ : CechF ⟶ KplusToDplusModX ⋙ RΓplus,
      IsModuleCechToDerivedGlobalSectionsComparison X 𝒰 τ ∧
        CommSq
          (((derivedTensorΓ.map (τ.app M)).app ((CechF).obj K)) ≫
            ((derivedTensorΓ.obj ((RΓplus).obj ((KplusToDplusModX).obj M))).map
              (τ.app K)))
          (cechTensorCounit K M ≫ naiveCupProduct K M)
          (relativeDerivedCupProduct
              leftDerivedPullback
              RΓplus
              globalSectionsAdj
              derivedTensorX
              derivedTensorΓ
              pullbackTensorIso
              ((KplusToDplusModX).obj K)
              ((KplusToDplusModX).obj M) ≫
            (RΓplus).map (sourceTensorCounit K M))
          (τ.app (sourceTensorComplex K M)) := by
  obtain ⟨τ, hτ⟩ := exists_moduleCechToDerivedGlobalSections X 𝒰 h𝒰
  exact ⟨τ, hτ,
    moduleCechToDerivedGlobalSections_tensor_naiveCupProduct_commSq
      𝒰 leftDerivedPullback globalSectionsAdj derivedTensorX derivedTensorΓ
      pullbackTensorIso sourceTensorComplex cechTensorComplex cechTensorCounit
      naiveCupProduct sourceTensorCounit pullbackCompatibility τ hτ K M⟩

end

end AlgebraicGeometry.RingedSpace
