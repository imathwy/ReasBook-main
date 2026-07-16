import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import StacksProject_2024.stacks_project.Chap20.Definition_20_49_1
import StacksProject_2024.stacks_project.Chap20.RingedSpaceOpensModuleCategory
import StacksProject_2024.stacks_project.Chap21.Definition_21_47_1

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open RingedSite
open RingedSite.Hom
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "CpxOX" => CochainComplex ModX ℤ
local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "SiteModX" => ModuleCat (opensRingedSite X)
local notation "SiteDModX" => RingedSite.Hom.ModuleDerived (opensRingedSite X)

section

variable [HasBinaryProducts (opensRingedSite X).carrier]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : (opensRingedSite X).carrier,
  (localizedRestriction (opensRingedSite X) U).Additive]
variable [∀ U : (opensRingedSite X).carrier,
  PreservesFiniteLimits (localizedRestriction (opensRingedSite X) U)]
variable [∀ U : (opensRingedSite X).carrier,
  PreservesFiniteColimits (localizedRestriction (opensRingedSite X) U)]
variable [CategoryWithHomology (ModuleCat (opensRingedSite X))]
variable [∀ U : (opensRingedSite X).carrier,
  CategoryWithHomology (ModuleCat ((opensRingedSite X).localization U))]

/-- The Chapter 20 open-cover owner agrees with the canonical Chapter 21 perfectness owner on the
opens ringed site of `X`. -/
theorem CochainComplex.isPerfect_iff_opensRingedSiteIsPerfect
    (E : CpxOX) :
    CochainComplex.IsPerfect E ↔
      (RingedSite.CochainComplex.IsPerfect : CochainComplex SiteModX ℤ → Prop) E := by
  sorry

namespace DerivedCategory

/-- The Chapter 20 derived-perfectness owner agrees with the canonical Chapter 21 owner on the
opens ringed site of `X`. -/
theorem isPerfect_iff_opensRingedSiteIsPerfect
    (E : DModX) :
    IsPerfect E ↔ (RingedSite.Hom.ModuleDerived.IsPerfect : SiteDModX → Prop) E := by
  sorry

end DerivedCategory

end

end AlgebraicGeometry.RingedSpace
