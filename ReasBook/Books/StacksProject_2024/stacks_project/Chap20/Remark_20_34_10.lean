import StacksProject_2024.Chap15.Definition_15_59_13
import StacksProject_2024.Chap15.Lemma_15_59_14
import StacksProject_2024.Chap21.Lemma_21_33_1_core
import StacksProject_2024.Chap20.Definition_20_26_14
import StacksProject_2024.Chap20.Lemma_20_34_4
import StacksProject_2024.Chap20.Remark_20_34_9

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped DerivedTensorProduct
open scoped RingedSpaceDerivedTensor

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

open scoped RingedSpaceClosedSubsetDerived
open scoped RingedSpaceClosedSubsetGlobalSectionsWithSupport

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DModZ" => closedSubsetModuleDerived X Z
local notation "DΓX" => DerivedCategory (ModuleCat (globalSectionsRing X))
local notation "DΓTensor" => CategoryTheory.derivedTensorProduct
local notation "RΓ" => moduleDerivedGlobalSections X
local notation "RΓZModel" => i⋆[hZ] ⋙ RΓ
local notation "RΓWithSupportModel" => R𝓗[hZ] ⋙ RΓZModel

/-- Tensoring on the left by a fixed object and mapping the right factor via the global-sections
derived tensor product. -/
noncomputable abbrev derivedTensorProductRightMap
    (A : DΓX) {B₁ B₂ : DΓX} (f : B₁ ⟶ B₂) :
    (DΓTensor B₁).obj A ⟶ (DΓTensor B₂).obj A :=
  (CategoryTheory.derivedTensorProduct_comm A B₁).hom ≫
    (DΓTensor A).map f ≫
    (CategoryTheory.derivedTensorProduct_comm B₂ A).hom

/- Domain-style sampling for Remark 20.34.10:
- primary domain: cup products on derived global sections with support for module sheaves on a
  ringed space;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.derivedTensorProduct`,
  `CategoryTheory.derivedTensorProduct`,
  `closedSubsetModuleGlobalSectionsWithSupportDerived X Z hZ`,
  `CategoryTheory.relativeDerivedCupProduct`,
  `moduleDerivedGlobalSections`;
- best owner abstraction:
  `source-facing`: the supported cup product, represented here by the model-side morphism
    `RΓ(X, K) ⊗^L RΓ_Z(X, M) ⟶ RΓ(X, i_* R𝓗_Z(K ⊗^L M))`
    before transporting across the comparison of Lemma 20.34.4;
  `core/canonical`: the supported global-sections owner
    `closedSubsetModuleGlobalSectionsWithSupportDerived X Z hZ` from Lemma 20.34.4, together with
    the canonical tensor owners
    `AlgebraicGeometry.RingedSpace.derivedTensorProduct`,
    `CategoryTheory.derivedTensorProduct`, and the canonical closed-subset cup-product owner
    `CategoryTheory.relativeDerivedCupProduct`;
  `bridge/view`: the fixed implementation
    `R𝓗[hZ] ⋙ (i⋆[hZ] ⋙ RΓ)` together with the restriction map on derived global sections and the
    pushforward-side tensor comparison from supported objects on `Z` to ambient objects on `X`.

Primitive data are therefore the chosen restriction functor and closed-subset derived
global-sections adjunction for the canonical model `i⋆[hZ] ⋙ RΓ`, together with the Z-side tensor
data and the pushforward-side comparison from Remark 20.34.9. The X-side and global-sections
tensor owners are already fixed upstream, so this file should reuse them directly rather than
keeping parallel tensor-functor or braiding parameters. -/

/- Remark 20.34.10: the Z-side cup product is the generic owner
`CategoryTheory.relativeDerivedCupProduct`, specialized to the closed-subset model
`RΓZModel = i⋆[hZ] ⋙ RΓ`. The source-facing supported cup product is characterized by the
comparison of Lemma 20.34.4 against that model-side composite. -/
variable (restrictionToClosedSubset : DModX ⥤ DModZ)
variable (leftDerivedPullbackZ : DΓX ⥤ DModZ)
variable (globalSectionsAdjZ : leftDerivedPullbackZ ⊣ i⋆[hZ] ⋙ RΓ)
variable (derivedTensorZ : DModZ ⥤ DModZ ⥤ DModZ)
variable
    (pullbackTensorIsoZ :
      ∀ (A B : DΓX),
        leftDerivedPullbackZ.obj (A ⊗[globalSectionsRing X]^L B) ≅
          ((derivedTensorZ.obj (leftDerivedPullbackZ.obj A)).obj
            (leftDerivedPullbackZ.obj B)))
variable
    (pushforwardTensorToAmbient :
      ∀ (K M : DModX),
        (i⋆[hZ]).obj
            ((derivedTensorZ.obj (restrictionToClosedSubset.obj K)).obj
              ((R𝓗[hZ]).obj M)) ⟶
          K ⊗^L M)

/-
Remark 20.34.10 uses `CategoryTheory.relativeDerivedCupProduct` on the closed-subset model
`RΓZModel = i⋆[hZ] ⋙ RΓ`.
-/
#check
  (CategoryTheory.relativeDerivedCupProduct leftDerivedPullbackZ RΓZModel globalSectionsAdjZ
    derivedTensorZ DΓTensor pullbackTensorIsoZ)

/-- The model-side forget-support morphism
`RΓ(X, i_* R𝓗_Z(M)) ⟶ RΓ(X, M)` attached to Lemma 20.34.4. -/
private noncomputable abbrev closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupportModel :
    RΓWithSupportModel ⟶ RΓ :=
  (Functor.associator (R𝓗[hZ]) (i⋆[hZ]) RΓ).hom ≫
    Functor.whiskerRight
      (closedSubsetModulePushforwardDerivedAdjunction X Z hZ).counit
      RΓ

/-- Remark 20.34.10: a morphism
`RΓ(X, K) ⊗^L RΓ_Z(X, M) ⟶ RΓ_Z(X, K ⊗^L M)`
realizes a chosen model-side cup product on `RΓ(X, i_* R𝓗_Z(K ⊗^L M))` if, after postcomposing
with the comparison of Lemma 20.34.4 on the target, it becomes that model-side morphism. -/
@[stacks 0G76]
def closedSubsetSectionsWithSupportDerivedCupProductModel
    (K M : DModX)
    (cupProduct :
      ((RΓ).obj K) ⊗[globalSectionsRing X]^L ((RΓ_[hZ]).obj M) ⟶
        (RΓ_[hZ]).obj (K ⊗^L M))
    (modelCupProduct :
      ((RΓ).obj K) ⊗[globalSectionsRing X]^L ((RΓ_[hZ]).obj M) ⟶
        (RΓWithSupportModel).obj (K ⊗^L M)) : Prop :=
  cupProduct ≫
      (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X Z hZ).app (K ⊗^L M) =
    modelCupProduct

/-- Companion model-side square for Remark 20.34.10: the canonical closed-subset model cup
product commutes with the forget-support morphisms to the ordinary cup product. -/
def ClosedSubsetSectionsWithSupportDerivedCupProductModelForgetSupportCommSq
    (globalCupProduct :
      ∀ (K M : DModX),
        ((RΓ).obj K) ⊗[globalSectionsRing X]^L ((RΓ).obj M) ⟶
          (RΓ).obj (K ⊗^L M))
    (K M : DModX)
    (modelCupProduct :
      ((RΓ).obj K) ⊗[globalSectionsRing X]^L ((RΓ_[hZ]).obj M) ⟶
        (RΓWithSupportModel).obj (K ⊗^L M)) : Prop :=
  CommSq
    modelCupProduct
    (derivedTensorProductRightMap
      ((RΓ).obj K)
      ((closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X Z hZ).app M))
    ((closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupportModel hZ).app (K ⊗^L M))
    (globalCupProduct K M)

/-- The canonical supported cup product of Remark 20.34.10 intertwines the forget-support
morphisms with the ordinary cup product whenever its model-side realization does. -/
theorem closedSubsetSectionsWithSupportDerivedCupProduct_forgetSupport_commSq
    (globalCupProduct :
      ∀ (K M : DModX),
        ((RΓ).obj K) ⊗[globalSectionsRing X]^L ((RΓ).obj M) ⟶
          (RΓ).obj (K ⊗^L M))
    (K M : DModX)
    (cupProduct :
      ((RΓ).obj K) ⊗[globalSectionsRing X]^L ((RΓ_[hZ]).obj M) ⟶
        (RΓ_[hZ]).obj (K ⊗^L M))
    (modelCupProduct :
      ((RΓ).obj K) ⊗[globalSectionsRing X]^L ((RΓ_[hZ]).obj M) ⟶
        (RΓWithSupportModel).obj (K ⊗^L M))
    (hcupProduct :
      closedSubsetSectionsWithSupportDerivedCupProductModel hZ K M cupProduct modelCupProduct)
    (hmodel :
      ClosedSubsetSectionsWithSupportDerivedCupProductModelForgetSupportCommSq
        hZ
        globalCupProduct
        K
        M
        modelCupProduct) :
    CommSq
      cupProduct
      (derivedTensorProductRightMap
        ((RΓ).obj K)
        ((closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X Z hZ).app M))
      ((closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X Z hZ).app
        (K ⊗^L M))
      (globalCupProduct K M) := by
  dsimp [closedSubsetSectionsWithSupportDerivedCupProductModel] at hcupProduct
  dsimp [ClosedSubsetSectionsWithSupportDerivedCupProductModelForgetSupportCommSq] at hmodel
  refine CommSq.mk ?_
  calc
    cupProduct ≫
        (closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X Z hZ).app (K ⊗^L M) =
      cupProduct ≫
          (closedSubsetModuleGlobalSectionsWithSupportDerivedComparison X Z hZ).app (K ⊗^L M) ≫
        (closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupportModel hZ).app
          (K ⊗^L M) := by
      rfl
    _ =
      modelCupProduct ≫
        (closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupportModel hZ).app
          (K ⊗^L M) := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            t ≫
              (closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupportModel hZ).app
                (K ⊗^L M))
          hcupProduct
    _ =
      derivedTensorProductRightMap
          ((RΓ).obj K)
          ((closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X Z hZ).app M) ≫
        globalCupProduct K M := by
      exact hmodel.w

end

end AlgebraicGeometry.RingedSpace
