import StacksProject_2024.stacks_project.Chap20.Definition_20_26_14_Core
import StacksProject_2024.stacks_project.Chap20.Perfect_on_opens_ringed_site
import StacksProject_2024.stacks_project.Chap21.Lemma_21_47_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open RingedSite.Hom.ModuleDerived
open TopologicalSpace
open scoped RingedSpaceDerivedTensor

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

/-
Domain-style sampling for Lemma 20.49.8:
- primary domain: perfect objects of `D(𝒪_X)` and their closure under the canonical derived
  tensor product on a ringed space;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `DerivedCategory.isPerfect_iff_opensRingedSiteIsPerfect`,
  `RingedSite.Hom.ModuleDerived.IsPerfect.tensor`,
  `opensRingedSite`;
- best owner abstraction:
  `source-facing`: the Chapter 20 tensor-closure statement for perfect objects on a ringed space;
  `core/canonical`: the opens-ringed-site tensor theorem
    `RingedSite.Hom.ModuleDerived.IsPerfect.tensor`;
  `bridge/view`: the perfectness identification
    `DerivedCategory.isPerfect_iff_opensRingedSiteIsPerfect`.
- primitive vs. derived:
  primitive data are the objects `K`, `L` and their perfectness hypotheses;
  the tensor-closure conclusion is obtained by specializing the opens-ringed-site perfect-tensor
  theorem along the canonical bridge above.
-/
variable {X : RingedSpace.{u}}
local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "SiteDModX" => RingedSite.Hom.ModuleDerived (opensRingedSite X)
local notation "SiteIsPerfect" => (IsPerfect : SiteDModX → Prop)

variable [HasBinaryProducts (opensRingedSite X).carrier]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [hCategoryWithHomology : CategoryWithHomology X.Modules]
variable [hHasCountableCoproducts : HasCountableCoproducts X.Modules]
variable [hMonoidalCategory : MonoidalCategory X.Modules]
variable [hMonoidalPreadditive : MonoidalPreadditive X.Modules]
variable [hHasColimits : HasColimits X.Modules]
variable [hTensorAdditive : (curriedTensor X.Modules).Additive]
variable [hTensorObjAdditive : ∀ ℱ : X.Modules, ((curriedTensor X.Modules).obj ℱ).Additive]
variable [hTensorMapBifunctor : ∀ (ℱ 𝒢 : CochainComplex X.Modules ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor X.Modules)]
variable [∀ U : (opensRingedSite X).carrier,
  (RingedSite.Hom.localizedRestriction (opensRingedSite X) U).Additive]
variable [∀ U : (opensRingedSite X).carrier,
  PreservesFiniteLimits (RingedSite.Hom.localizedRestriction (opensRingedSite X) U)]
variable [∀ U : (opensRingedSite X).carrier,
  PreservesFiniteColimits (RingedSite.Hom.localizedRestriction (opensRingedSite X) U)]
variable [∀ U : (opensRingedSite X).carrier,
  CategoryWithHomology (RingedSite.Hom.ModuleCat ((opensRingedSite X).localization U))]
variable [∀ U : (opensRingedSite X).carrier,
  MonoidalCategory (RingedSite.Hom.ModuleDerived ((opensRingedSite X).localization U))]
-- Proof sketch: transport the perfectness hypotheses to the canonical opens-ringed-site owner via
-- `DerivedCategory.isPerfect_iff_opensRingedSiteIsPerfect`, apply
-- `RingedSite.Hom.ModuleDerived.IsPerfect.tensor`, and transport the conclusion back.
/-- Lemma 20.49.8: for a ringed space `(X, 𝒪_X)`, the derived tensor product of two perfect
objects of `D(𝒪_X)` is again perfect. -/
@[stacks 09J5]
theorem tensor_isPerfect_of_isPerfect
    (K L : DModX)
    (hK : DerivedCategory.IsPerfect K) (hL : DerivedCategory.IsPerfect L) :
    DerivedCategory.IsPerfect (K ⊗^L L) := by
  have hKSite : SiteIsPerfect K :=
    (DerivedCategory.isPerfect_iff_opensRingedSiteIsPerfect K).1 hK
  have hLSite : SiteIsPerfect L :=
    (DerivedCategory.isPerfect_iff_opensRingedSiteIsPerfect L).1 hL
  have hTensorSite : SiteIsPerfect (K ⊗^L L) := by
    simpa using IsPerfect.tensor hKSite hLSite
  exact (DerivedCategory.isPerfect_iff_opensRingedSiteIsPerfect (K ⊗^L L)).2 hTensorSite

end

end AlgebraicGeometry.RingedSpace
