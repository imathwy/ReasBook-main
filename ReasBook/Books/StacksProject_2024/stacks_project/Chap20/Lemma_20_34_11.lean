import StacksProject_2024.Chap20.Remark_20_34_10

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped DerivedTensorProduct
open scoped RingedSpaceDerivedTensor

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

open scoped RingedSpaceClosedSubsetDerived
open scoped RingedSpaceClosedSubsetGlobalSectionsWithSupport

/- Domain-style sampling for Lemma 20.34.11:
- primary domain: derived global sections with support and compatibility of the resulting
  cohomology cup product with the forget-support morphism;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.derivedTensorProduct`,
  `CategoryTheory.derivedTensorProduct`,
  `CategoryTheory.CommSq`,
  `DerivedCategory.homologyFunctor`,
  `closedSubsetModuleGlobalSectionsWithSupportDerived X Z hZ`,
  `closedSubsetSectionsWithSupportDerivedCupProduct_forgetSupport_commSq`;
- best owner abstraction:
  `source-facing`: the degree-`n` cohomology compatibility square for cup products with support;
  `core/canonical`: the source-facing supported cup-product compatibility theorem
    `closedSubsetSectionsWithSupportDerivedCupProduct_forgetSupport_commSq` from
    Remark 20.34.10,
    together with `DerivedCategory.homologyFunctor`;
  `bridge/view`: the Prop-level hypotheses
    `closedSubsetSectionsWithSupportDerivedCupProductModel` and
    `ClosedSubsetSectionsWithSupportDerivedCupProductModelForgetSupportCommSq`
    from Remark 20.34.10.

Primitive data are the canonical closed-subset global-sections model `i⋆ ⋙ RΓ`, the
adjunction-level data determining the closed-subset cup product, and the ordinary/supported
cup-product morphisms. Degree cohomology and the commuting-square formulation are derived API
from those owners. -/

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
local notation "RΓ" => moduleDerivedGlobalSections X
local notation "RΓWithSupportModel" => R𝓗[hZ] ⋙ i⋆[hZ] ⋙ RΓ

private abbrev H (n : ℤ) := DerivedCategory.homologyFunctor (ModuleCat (globalSectionsRing X)) n

-- Proof sketch: the derived-category square is the canonical compatibility between the supported
-- cup product and the forget-support map. Applying `H n` to that square yields the source-facing
-- compatibility square on degree-`n` cohomology objects.
/-- Lemma 20.34.11: with the notation of Remarks 20.34.9 and 20.34.10, the degree-`n`
cohomology square induced by a supported cup product commutes with the forget-support morphisms to
the ordinary cup-product morphism as soon as its model-side realization does. -/
@[stacks 0G77]
theorem closedSubsetRestriction_sectionsWithSupportDerived_cupProduct_forgetSupport_commSq
    (n : ℤ) (K M : DModX)
    (globalCupProduct :
      ∀ (K M : DModX),
        ((RΓ).obj K) ⊗[globalSectionsRing X]^L ((RΓ).obj M) ⟶
          (RΓ).obj (K ⊗^L M))
    (cupProduct :
      ((RΓ).obj K) ⊗[globalSectionsRing X]^L ((RΓ_[hZ]).obj M) ⟶
        (RΓ_[hZ]).obj (K ⊗^L M))
    (modelCupProduct :
      ((RΓ).obj K) ⊗[globalSectionsRing X]^L ((RΓ_[hZ]).obj M) ⟶
        (RΓWithSupportModel).obj (K ⊗^L M))
    (hcupProduct :
      closedSubsetSectionsWithSupportDerivedCupProductModel
        hZ
        K
        M
        cupProduct
        modelCupProduct)
    (hmodel :
      ClosedSubsetSectionsWithSupportDerivedCupProductModelForgetSupportCommSq
        hZ
        globalCupProduct
        K
        M
        modelCupProduct) :
    CommSq
      ((H n).map cupProduct)
      ((H n).map
        (derivedTensorProductRightMap
          ((RΓ).obj K)
          ((closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X Z hZ).app M)))
      ((H n).map
        ((closedSubsetModuleGlobalSectionsWithSupportDerivedForgetSupport X Z hZ).app
          (K ⊗^L M)))
      ((H n).map (globalCupProduct K M)) := by
  let sq :=
    closedSubsetSectionsWithSupportDerivedCupProduct_forgetSupport_commSq
      hZ
      globalCupProduct
      K
      M
      cupProduct
      modelCupProduct
      hcupProduct
      hmodel
  simpa using sq.map (H n)

end

end AlgebraicGeometry.RingedSpace
