import StacksProject_2024.Chap21.Lemma_21_45_5
import StacksProject_2024.Chap21.Lemma_21_47_4

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open RingedSite.Hom (ModuleCat ModuleDerived localizedRestriction)
open scoped RingedSiteDerivedTensor

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

/- Domain-style sampling for Lemma 21.47.7:
- primary domain: perfect objects in the derived category of `\mathcal O_X`-modules on a ringed
  site and their behavior under the canonical derived tensor product;
- sampled owner declarations:
  `SheafOfModules.RingedSite.derivedTensorProduct`,
  `RingedSite.DerivedCategory.IsPerfect`,
  `RingedSite.Hom.ModuleDerived.IsPseudoCoherent.tensor`,
  `RingedSite.Hom.ModuleDerived.LocallyHasFiniteTorDimension`,
  `SheafOfModules.RingedSite.isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension`;
- best owner abstraction:
  `source-facing`: the textbook perfectness statement for `K ⊗^L L`;
  `core/canonical`: the owner predicates `K.IsPerfect` and
    `K.LocallyHasFiniteTorDimension`, together with the Chapter 21 derived tensor owner
    `derivedTensorProduct` and the existing owner theorem `IsPseudoCoherent.tensor`;
  `bridge/view`: the source-facing notation `K ⊗^L L`, while the later localized monoidal tensor
    comparison `K ⊗ L ≅ K ⊗^L L` remains separate bridge material from `Lemma_21_48_5`.
- primitive data: the ringed site `X`, the derived objects `K`, `L`, and the tensor owner on
  `ModuleDerived X`;
- derived API: the source-facing perfectness theorem below, together with the local finite
  Tor-dimension closure input used inside its proof.

Source/core/bridge triage:
- `source-facing`: `RingedSite.Hom.ModuleDerived.IsPerfect.tensor`;
- `core/canonical`: the existing owner predicates `K.IsPseudoCoherent`,
  `K.LocallyHasFiniteTorDimension`, the owner theorem `IsPseudoCoherent.tensor`, and the
  perfectness criterion from Lemma `21.47.4`, all over the owner `derivedTensorProduct`;
- `bridge/view`: the bundled-owner notation `K ⊗^L L` and the later comparison isomorphism to the
  localized monoidal tensor.

This file keeps the theorem name in the existing namespace
`RingedSite.Hom.ModuleDerived`, but the tensor surface is expressed on the commutative-site
presentation `X := RingedSite.ofCommRingSheaf J 𝒪` so that `K ⊗^L L` is the actual Chapter 21
derived tensor owner. The localized monoidal tensor remains bridge material, not the main owner
of the theorem below. -/

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, ((J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v}))]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, ((J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [HasBinaryProducts C]
variable [CategoryWithHomology (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [HasColimits (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ M : SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)).obj M).Additive]
variable [∀ (K L : CochainComplex (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L
    (curriedTensor (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪))]
variable [∀ U : C, (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).Additive]
variable [∀ U : C,
  PreservesFiniteLimits (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
variable [∀ U : C,
  PreservesFiniteColimits (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
variable [∀ U : C,
  CategoryWithHomology (SheafOfModules.RingedSite.ringedSiteModuleCategory (J.over U) (𝒪.over U))]
variable [∀ U : C,
  MonoidalCategory (ModuleDerived ((RingedSite.ofCommRingSheaf J 𝒪).localization U))]

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "DMod" => ModuleDerived X

local instance : Abelian (ModuleCat X) :=
  SheafOfModules.instAbelian (RingedSite.ofCommRingSheaf J 𝒪).structureSheaf

local instance (U : C) :
    Abelian (ModuleCat ((RingedSite.ofCommRingSheaf J 𝒪).localization U)) :=
  SheafOfModules.instAbelian ((RingedSite.ofCommRingSheaf J 𝒪).localization U).structureSheaf

namespace RingedSite.Hom
namespace ModuleDerived

open SheafOfModules.RingedSite

local notation "FiniteTor" => (LocallyHasFiniteTorDimension : DMod → Prop)
local notation "Perfect" => (IsPerfect : DMod → Prop)

/-- The derived tensor product of locally finite-Tor-dimension objects again locally has finite
Tor dimension. -/
theorem LocallyHasFiniteTorDimension.tensor
    {K L : DMod}
    (hK : K.LocallyHasFiniteTorDimension)
    (hL : L.LocallyHasFiniteTorDimension) :
    FiniteTor (K ⊗^L L) := by
  sorry

/-- Lemma 21.47.7: the derived tensor product of two perfect objects of `D(𝒪_X)` is
again perfect. -/
@[stacks 09JB]
theorem IsPerfect.tensor
    {K L : DMod}
    (hK : K.IsPerfect)
    (hL : L.IsPerfect) :
    Perfect (K ⊗^L L) := by
  sorry

end ModuleDerived
end RingedSite.Hom

end
