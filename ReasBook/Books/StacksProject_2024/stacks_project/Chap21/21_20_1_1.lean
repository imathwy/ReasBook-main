import Mathlib
import StacksProject_2024.Chap18.Lemma_18_16_6
import StacksProject_2024.Chap18.Lemma_18_19_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] [HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)
variable [HasSheafify (J.over U) AddCommGrpCat.{u}]

local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [Abelian Mod]
variable [Abelian (ringedSiteModuleCategory (J.over U) (𝒪.over U))]

local instance modulePreadditive : Preadditive Mod := Abelian.toPreadditive

local instance localizedModulePreadditive :
    Preadditive (ringedSiteModuleCategory (J.over U) (𝒪.over U)) := Abelian.toPreadditive

/- Domain-style sampling for the owner layer of Lemma 21.20.1:
- primary domain: localized lower shriek and restriction for sheaves of modules on a ringed site;
- sampled owner declarations:
  `ringedSiteLocalizedRestriction`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `exactFunctor`;
- best owner abstraction: the localized lower-shriek owner
  `ringedSiteLocalizedLowerShriek J 𝒪 U`, together with its adjunction to the Chapter 18 owner
  `ringedSiteLocalizedRestriction J 𝒪 U`;
- primitive data: only `J`, `𝒪`, and `U`;
- derived API: the exactness and adjunction companions below.

Source/core/bridge triage:
- `source-facing`: the localized lower shriek `j_{U!}` on module sheaves;
- `core/canonical`: `SheafOfModules.pullback (𝟙 ((ringSheaf J 𝒪).over U))` and
  `SheafOfModules.pullbackPushforwardAdjunction (𝟙 ((ringSheaf J 𝒪).over U))`;
- `bridge/view`: the Chapter 21 owner names below. -/

/-- The localized lower-shriek functor on module sheaves, i.e. the exact left adjoint to
localized restriction on the identity map of the localized structure sheaf. -/
abbrev ringedSiteLocalizedLowerShriek :
    ringedSiteModuleCategory (J.over U) (𝒪.over U) ⥤ ringedSiteModuleCategory J 𝒪 :=
  SheafOfModules.pullback (𝟙 ((ringSheaf J 𝒪).over U))

/-- Companion owner theorem: localized lower shriek is left adjoint to localized restriction. -/
noncomputable abbrev ringedSiteLocalizedLowerShriek_adjunction :
    ringedSiteLocalizedLowerShriek J 𝒪 U ⊣
      ringedSiteLocalizedRestriction J 𝒪 U := by
  simpa [ringedSiteLocalizedLowerShriek] using
    (SheafOfModules.pullbackPushforwardAdjunction (𝟙 ((ringSheaf J 𝒪).over U)))

/-- Companion owner theorem: localized lower shriek is exact. -/
noncomputable abbrev ringedSiteLocalizedLowerShriek_exact :
    exactFunctor
      (ringedSiteModuleCategory (J.over U) (𝒪.over U))
      (ringedSiteModuleCategory J 𝒪)
      (ringedSiteLocalizedLowerShriek J 𝒪 U) := by
  sorry

instance ringedSiteLocalizedLowerShriek_preservesFiniteLimits :
    PreservesFiniteLimits (ringedSiteLocalizedLowerShriek J 𝒪 U) :=
  (CategoryTheory.exactFunctor_iff
      (ringedSiteLocalizedLowerShriek J 𝒪 U)).mp
    (ringedSiteLocalizedLowerShriek_exact J 𝒪 U) |>.1

instance ringedSiteLocalizedLowerShriek_preservesFiniteColimits :
    PreservesFiniteColimits (ringedSiteLocalizedLowerShriek J 𝒪 U) :=
  (CategoryTheory.exactFunctor_iff
      (ringedSiteLocalizedLowerShriek J 𝒪 U)).mp
    (ringedSiteLocalizedLowerShriek_exact J 𝒪 U) |>.2

instance ringedSiteLocalizedLowerShriek_additive :
    (ringedSiteLocalizedLowerShriek J 𝒪 U).Additive := by
  have : PreservesBinaryBiproducts (ringedSiteLocalizedLowerShriek J 𝒪 U) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

end

end SheafOfModules.RingedSite
