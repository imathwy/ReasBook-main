import StacksProject_2024.stacks_project.Chap20.Definition_20_26_14_Core
import StacksProject_2024.stacks_project.Chap20.Lemma_20_34_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped RingedSpaceDerivedTensor

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

open scoped RingedSpaceClosedSubsetDerived

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

/- Domain-style sampling for Remark 20.34.9:
- primary domain: the closed-subset tensor comparison obtained by transposing a pushforward-side
  tensor morphism across `i⋆[hZ] ⊣ R𝓗[hZ]`;
- sampled owner declarations:
  `Adjunction.homEquiv`,
  `Adjunction.homEquiv_counit`,
  `AlgebraicGeometry.RingedSpace.derivedTensorProduct`,
  `CategoryTheory.CommSq`;
- source/core/bridge triage:
  `source-facing`: the canonical morphism
    `K|_Z ⊗^L_{𝒪_X|_Z} R𝓗_Z(M) ⟶ R𝓗_Z(K ⊗^L_{𝒪_X} M)`;
  `core/canonical`: `Adjunction.homEquiv` for `i⋆[hZ] ⊣ R𝓗[hZ]` together with the ambient derived
    tensor owner `⊗^L` on `D(𝒪_X)`;
  `bridge/view`: the `Z`-side tensor owner, the pushforward-side tensor comparison
    `(i⋆[hZ]).obj (K|_Z ⊗ R𝓗_Z(M)) ⟶ K ⊗^L M`.

The source-facing morphism is already the adjunction transpose of that pushforward-side composite,
so this file keeps the canonical `Adjunction.homEquiv` surface, reuses the chapter owner `⊗^L`
  on `D(𝒪_X)`, and records the pushforward compatibility as a `CommSq` bridge. -/

variable (restrictionToClosedSubset : DModX ⥤ DModZ)
variable (derivedTensorZ : DModZ ⥤ DModZ ⥤ DModZ)
variable
    (pushforwardTensorToAmbient :
      ∀ (K M : DModX),
        (i⋆[hZ]).obj
          ((derivedTensorZ.obj (restrictionToClosedSubset.obj K)).obj ((R𝓗[hZ]).obj M)) ⟶
        K ⊗^L M)

/-- The pushforward-side tensor comparison in Remark 20.34.9. -/
noncomputable abbrev closedSubsetRestrictionTensor_sectionsWithSupportDerived_pushforward
    (restrictionToClosedSubset : DModX ⥤ DModZ)
    (derivedTensorZ : DModZ ⥤ DModZ ⥤ DModZ)
    (pushforwardTensorToAmbient :
      ∀ (K M : DModX),
        (i⋆[hZ]).obj
          ((derivedTensorZ.obj (restrictionToClosedSubset.obj K)).obj ((R𝓗[hZ]).obj M)) ⟶
        K ⊗^L M)
    (K M : DModX) :
    (i⋆[hZ]).obj
      ((derivedTensorZ.obj (restrictionToClosedSubset.obj K)).obj ((R𝓗[hZ]).obj M)) ⟶
    K ⊗^L M :=
  pushforwardTensorToAmbient K M

/-- Remark 20.34.9: the canonical morphism
`K|_Z ⊗^L_{𝒪_X|_Z} R𝓗_Z(M) ⟶ R𝓗_Z(K ⊗^L_{𝒪_X} M)`
is the `Adjunction.homEquiv` transpose of the pushforward-side tensor comparison. -/
@[stacks 0G75]
noncomputable abbrev closedSubsetRestrictionTensor_sectionsWithSupportDerived
    (restrictionToClosedSubset : DModX ⥤ DModZ)
    (derivedTensorZ : DModZ ⥤ DModZ ⥤ DModZ)
    (pushforwardTensorToAmbient :
      ∀ (K M : DModX),
        (i⋆[hZ]).obj
          ((derivedTensorZ.obj (restrictionToClosedSubset.obj K)).obj ((R𝓗[hZ]).obj M)) ⟶
        K ⊗^L M)
    (K M : DModX) :
    ((derivedTensorZ.obj (restrictionToClosedSubset.obj K)).obj ((R𝓗[hZ]).obj M)) ⟶
      (R𝓗[hZ]).obj (K ⊗^L M) :=
  ((closedSubsetModulePushforwardDerivedAdjunction X Z hZ).homEquiv
      ((derivedTensorZ.obj (restrictionToClosedSubset.obj K)).obj ((R𝓗[hZ]).obj M))
      (K ⊗^L M))
    (closedSubsetRestrictionTensor_sectionsWithSupportDerived_pushforward
      hZ restrictionToClosedSubset derivedTensorZ pushforwardTensorToAmbient K M)

/-- Applying `i_*` to the canonical tensor map of Remark 20.34.9 and then the counit of
`i⋆[hZ] ⊣ R𝓗[hZ]` recovers the explicit pushforward-side tensor comparison. -/
theorem closedSubsetRestrictionTensor_sectionsWithSupportDerived_commSq
    (restrictionToClosedSubset : DModX ⥤ DModZ)
    (derivedTensorZ : DModZ ⥤ DModZ ⥤ DModZ)
    (pushforwardTensorToAmbient :
      ∀ (K M : DModX),
        (i⋆[hZ]).obj
          ((derivedTensorZ.obj (restrictionToClosedSubset.obj K)).obj ((R𝓗[hZ]).obj M)) ⟶
        K ⊗^L M)
    (K M : DModX) :
    CommSq
      ((i⋆[hZ]).map
        (closedSubsetRestrictionTensor_sectionsWithSupportDerived
          hZ restrictionToClosedSubset derivedTensorZ pushforwardTensorToAmbient K M))
      (closedSubsetRestrictionTensor_sectionsWithSupportDerived_pushforward
        hZ restrictionToClosedSubset derivedTensorZ pushforwardTensorToAmbient K M)
      ((closedSubsetModulePushforwardDerivedAdjunction X Z hZ).counit.app (K ⊗^L M))
      (𝟙 (K ⊗^L M)) := by
  let A : DModZ :=
    (derivedTensorZ.obj (restrictionToClosedSubset.obj K)).obj ((R𝓗[hZ]).obj M)
  let B : DModX := K ⊗^L M
  let adj := closedSubsetModulePushforwardDerivedAdjunction X Z hZ
  let η : (i⋆[hZ]).obj A ⟶ B :=
    closedSubsetRestrictionTensor_sectionsWithSupportDerived_pushforward
      hZ restrictionToClosedSubset derivedTensorZ pushforwardTensorToAmbient K M
  have hη :
      (i⋆[hZ]).map ((adj.homEquiv A B) η) ≫ adj.counit.app B =
        η := by
    simpa using
      (adj.homEquiv_counit A B ((adj.homEquiv A B) η)).symm
  refine CommSq.mk ?_
  simpa
    [A, B, adj, η, closedSubsetRestrictionTensor_sectionsWithSupportDerived,
      closedSubsetRestrictionTensor_sectionsWithSupportDerived_pushforward]
    using hη

/-- Companion equality form of the `CommSq` in Remark 20.34.9. -/
theorem closedSubsetRestrictionTensor_sectionsWithSupportDerived_comp_counit
    (restrictionToClosedSubset : DModX ⥤ DModZ)
    (derivedTensorZ : DModZ ⥤ DModZ ⥤ DModZ)
    (pushforwardTensorToAmbient :
      ∀ (K M : DModX),
        (i⋆[hZ]).obj
          ((derivedTensorZ.obj (restrictionToClosedSubset.obj K)).obj ((R𝓗[hZ]).obj M)) ⟶
        K ⊗^L M)
    (K M : DModX) :
    (i⋆[hZ]).map
        (closedSubsetRestrictionTensor_sectionsWithSupportDerived
          hZ restrictionToClosedSubset derivedTensorZ pushforwardTensorToAmbient K M) ≫
      (closedSubsetModulePushforwardDerivedAdjunction X Z hZ).counit.app (K ⊗^L M) =
    closedSubsetRestrictionTensor_sectionsWithSupportDerived_pushforward
      hZ restrictionToClosedSubset derivedTensorZ pushforwardTensorToAmbient K M := by
  simpa using
    (closedSubsetRestrictionTensor_sectionsWithSupportDerived_commSq
      hZ restrictionToClosedSubset derivedTensorZ pushforwardTensorToAmbient K M).w

end

end AlgebraicGeometry.RingedSpace
