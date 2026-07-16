import StacksProject_2024.stacks_project.Chap18.Lemma_18_19_2
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategoryBasic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open SheafOfModules.RingedSite
  (ringSheaf ringedSiteLocalizedRestriction ringedSiteModuleCategory)

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
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "ModU" => ringedSiteModuleCategory (J.over U) (𝒪.over U)

/- Domain-style sampling for the owner layer of Lemma 21.20.1:
- primary domain: localized lower shriek and restriction for sheaves of modules on a ringed site;
- sampled owner declarations:
  `ringedSiteLocalizedRestriction`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`;
- best owner abstraction: the localized lower-shriek owner
  `ringedSiteLocalizedLowerShriek J 𝒪 U` together with its adjunction to
  `ringedSiteLocalizedRestriction J 𝒪 U`.
-/

/-- The localized lower-shriek functor on module sheaves. -/
abbrev ringedSiteLocalizedLowerShriek :
    ringedSiteModuleCategory (J.over U) (𝒪.over U) ⥤ ringedSiteModuleCategory J 𝒪 :=
  SheafOfModules.pullback (𝟙 ((ringSheaf J 𝒪).over U))

/-- Companion owner theorem: localized lower shriek is left adjoint to localized restriction. -/
noncomputable abbrev ringedSiteLocalizedLowerShriek_adjunction :
    ringedSiteLocalizedLowerShriek J 𝒪 U ⊣
      ringedSiteLocalizedRestriction J 𝒪 U :=
  SheafOfModules.pullbackPushforwardAdjunction (𝟙 ((ringSheaf J 𝒪).over U))

/-- Companion owner theorem: localized lower shriek is exact. -/
theorem ringedSiteLocalizedLowerShriek_exact :
    exactFunctor ModU Mod (ringedSiteLocalizedLowerShriek J 𝒪 U) := by
  sorry

instance ringedSiteLocalizedLowerShriek_preservesFiniteLimits
    [Abelian Mod] [Abelian ModU] :
    PreservesFiniteLimits (ringedSiteLocalizedLowerShriek J 𝒪 U) := by
  let _ : Preadditive Mod := Abelian.toPreadditive
  let _ : Preadditive ModU := Abelian.toPreadditive
  exact (exactFunctor_iff (ringedSiteLocalizedLowerShriek J 𝒪 U)).mp
    (ringedSiteLocalizedLowerShriek_exact J 𝒪 U) |>.1

instance ringedSiteLocalizedLowerShriek_preservesFiniteColimits
    [Abelian Mod] [Abelian ModU] :
    PreservesFiniteColimits (ringedSiteLocalizedLowerShriek J 𝒪 U) := by
  let _ : Preadditive Mod := Abelian.toPreadditive
  let _ : Preadditive ModU := Abelian.toPreadditive
  exact (exactFunctor_iff (ringedSiteLocalizedLowerShriek J 𝒪 U)).mp
    (ringedSiteLocalizedLowerShriek_exact J 𝒪 U) |>.2

instance ringedSiteLocalizedLowerShriek_additive
    [Abelian Mod] [Abelian ModU] :
    (ringedSiteLocalizedLowerShriek J 𝒪 U).Additive := by
  let _ : Preadditive Mod := Abelian.toPreadditive
  let _ : Preadditive ModU := Abelian.toPreadditive
  have : PreservesBinaryBiproducts (ringedSiteLocalizedLowerShriek J 𝒪 U) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts
      (ringedSiteLocalizedLowerShriek J 𝒪 U)
  exact Functor.additive_of_preservesBinaryBiproducts
    (ringedSiteLocalizedLowerShriek J 𝒪 U)

end

end SheafOfModules.RingedSite
