import StacksProject_2024.stacks_project.Chap20.Definition_20_48_1_Core
import StacksProject_2024.stacks_project.Chap20.RingedSpaceOpensModuleCategory
import StacksProject_2024.stacks_project.Chap21.Definition_21_46_1_Core

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]
variable [MonoidalCategory (DerivedCategory (Modules X))]

local notation "DMod" => DerivedCategory (Modules X)
local notation "OpensDMod" => RingedSite.Hom.ModuleDerived (opensRingedSite X)

local instance opensRingedSite_monoidalCategoryStruct :
    MonoidalCategoryStruct (RingedSite.Hom.ModuleDerived (opensRingedSite X)) := by
  change MonoidalCategoryStruct (DerivedCategory (Modules X))
  exact
    (inferInstance : MonoidalCategory (DerivedCategory (Modules X))).toMonoidalCategoryStruct

/-- The Chapter 20 tor-amplitude owner agrees with the Chapter 21 tor-amplitude owner on the
opens ringed site of `X`. -/
theorem hasTorAmplitudeIn_iff_opensRingedSiteHasTorAmplitudeIn
    (E : OpensDMod) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      SheafOfModules.RingedSite.HasTorAmplitudeIn E a b := by
  sorry

end

end AlgebraicGeometry.RingedSpace
