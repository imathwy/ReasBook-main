import StacksProject_2024.stacks_project.Chap20.Definition_20_49_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_47_8

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [HasBinaryProducts (opensRingedSite X).carrier]
variable [∀ U : (opensRingedSite X).carrier,
  (localizedRestriction (opensRingedSite X) U).Additive]
variable [∀ U : (opensRingedSite X).carrier,
  PreservesFiniteLimits (localizedRestriction (opensRingedSite X) U)]
variable [∀ U : (opensRingedSite X).carrier,
  PreservesFiniteColimits (localizedRestriction (opensRingedSite X) U)]
variable [∀ U : (opensRingedSite X).carrier,
  CategoryWithHomology (ModuleCat ((opensRingedSite X).localization U))]

/- Domain-style sampling for Lemma 20.49.9:
- primary domain: perfect objects of `D(𝒪_X)` and their stability under direct summands;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.DerivedCategory.IsPerfect`,
  `CategoryTheory.ObjectProperty.IsStableUnderRetracts`,
  `SheafOfModules.RingedSite.isPerfect_isStableUnderRetracts`,
  `SheafOfModules.RingedSite.isPerfect_summands_of_biprod`,
  `opensRingedSite`;
- best owner abstraction:
  `source-facing`: the direct-summand clauses of Lemma `20.49.9` for a ringed space;
  `core/canonical`: the Chapter 21 perfectness owner `K.IsPerfect` on
    `ModuleDerived (opensRingedSite X)` together with its retract-stability API;
  `bridge/view`: `AlgebraicGeometry.RingedSpace.DerivedCategory.IsPerfect` is exactly the
    opens-ringed-site specialization of that owner, so the present file should only specialize the
    existing Chapter 21 retract/direct-summand API.

This file keeps the source-facing ringed-space specialization and exposes the direct-summand API
through the canonical `ObjectProperty.IsStableUnderRetracts` owner. -/

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "SiteDModX" => RingedSite.Hom.ModuleDerived (opensRingedSite X)
local notation "SiteIsPerfect" => (IsPerfect : SiteDModX → Prop)
local notation "PerfectObj" => (DerivedCategory.IsPerfect : ObjectProperty DModX)

/-- Perfect objects of `D(𝒪_X)` are stable under retracts/direct summands. -/
instance isPerfect_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts PerfectObj := by
  change ObjectProperty.IsStableUnderRetracts (SiteIsPerfect : ObjectProperty SiteDModX)
  exact SheafOfModules.RingedSite.isPerfect_isStableUnderRetracts

omit [∀ U : (opensRingedSite X).carrier, (localizedRestriction (opensRingedSite X) U).Additive]
  [∀ U : (opensRingedSite X).carrier,
    PreservesFiniteLimits (localizedRestriction (opensRingedSite X) U)]
  [∀ U : (opensRingedSite X).carrier,
    PreservesFiniteColimits (localizedRestriction (opensRingedSite X) U)] in
/-- Lemma 20.49.9: if `K ⊞ L` is a perfect object of `D(𝒪_X)`, then both summands are perfect. -/
@[stacks 08CS]
theorem isPerfect_summands_of_biprod
    (K L : DModX) [HasBinaryBiproduct K L] (hKL : DerivedCategory.IsPerfect (K ⊞ L)) :
    DerivedCategory.IsPerfect K ∧ DerivedCategory.IsPerfect L := by
  let K' : SiteDModX := K
  let L' : SiteDModX := L
  change SiteIsPerfect K' ∧ SiteIsPerfect L'
  change SiteIsPerfect (K' ⊞ L') at hKL
  exact SheafOfModules.RingedSite.isPerfect_summands_of_biprod K' L' hKL

omit [∀ U : (opensRingedSite X).carrier, (localizedRestriction (opensRingedSite X) U).Additive]
  [∀ U : (opensRingedSite X).carrier,
    PreservesFiniteLimits (localizedRestriction (opensRingedSite X) U)]
  [∀ U : (opensRingedSite X).carrier,
    PreservesFiniteColimits (localizedRestriction (opensRingedSite X) U)] in
/-- Lemma 20.49.9 (1): if `K ⊞ L` is a perfect object of `D(𝒪_X)`, then `K` is perfect. -/
@[stacks 08CS]
theorem isPerfect_left_of_biprod
    (K L : DModX) [HasBinaryBiproduct K L] (hKL : DerivedCategory.IsPerfect (K ⊞ L)) :
    DerivedCategory.IsPerfect K :=
  (isPerfect_summands_of_biprod K L hKL).1

omit [∀ U : (opensRingedSite X).carrier, (localizedRestriction (opensRingedSite X) U).Additive]
  [∀ U : (opensRingedSite X).carrier,
    PreservesFiniteLimits (localizedRestriction (opensRingedSite X) U)]
  [∀ U : (opensRingedSite X).carrier,
    PreservesFiniteColimits (localizedRestriction (opensRingedSite X) U)] in
/-- Lemma 20.49.9 (2): if `K ⊞ L` is a perfect object of `D(𝒪_X)`, then `L` is perfect. -/
@[stacks 08CS]
theorem isPerfect_right_of_biprod
    (K L : DModX) [HasBinaryBiproduct K L] (hKL : DerivedCategory.IsPerfect (K ⊞ L)) :
    DerivedCategory.IsPerfect L :=
  (isPerfect_summands_of_biprod K L hKL).2

end

end AlgebraicGeometry.RingedSpace
