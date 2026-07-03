import Mathlib
import StacksProject_2024.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "ModU" => ringedSiteModuleCategory (J.over U) (𝒪.over U)
local notation "DMod" => DerivedCategory Mod
local notation "DModU" => DerivedCategory ModU
local notation "Q" => (DerivedCategory.Q : CochainComplex Mod ℤ ⥤ DMod)
local notation "QU" => (DerivedCategory.Q : CochainComplex ModU ℤ ⥤ DModU)
local notation "Qis" => HomologicalComplex.quasiIso Mod (up ℤ)
local notation "QisU" => HomologicalComplex.quasiIso ModU (up ℤ)

private abbrev ringedSiteRingSheaf : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

variable [Abelian Mod]
variable [Abelian ModU]

/-- Extension by zero from the localized ringed site preserves finite limits. -/
private instance ringedSiteLocalizedExtensionByZero_preservesFiniteLimits :
    PreservesFiniteLimits
      (SheafOfModules.pullback (𝟙 ((ringedSiteRingSheaf J 𝒪).over U))) := sorry

/-- Extension by zero from the localized ringed site preserves finite colimits. -/
private instance ringedSiteLocalizedExtensionByZero_preservesFiniteColimits :
    PreservesFiniteColimits
      (SheafOfModules.pullback (𝟙 ((ringedSiteRingSheaf J 𝒪).over U))) := sorry

/-- Restriction to the localized ringed site preserves finite limits. -/
private instance ringedSiteLocalizedRestriction_preservesFiniteLimits :
    PreservesFiniteLimits
      (SheafOfModules.pushforward (𝟙 ((ringedSiteRingSheaf J 𝒪).over U))) := sorry

/-- Restriction to the localized ringed site preserves finite colimits. -/
private instance ringedSiteLocalizedRestriction_preservesFiniteColimits :
    PreservesFiniteColimits
      (SheafOfModules.pushforward (𝟙 ((ringedSiteRingSheaf J 𝒪).over U))) := sorry

/-- Extension by zero from the localized ringed site is additive. -/
private instance ringedSiteLocalizedExtensionByZero_additive :
    (SheafOfModules.pullback (𝟙 ((ringedSiteRingSheaf J 𝒪).over U))).Additive := sorry

/-- Restriction to the localized ringed site is additive. -/
private instance ringedSiteLocalizedRestriction_additive :
    (SheafOfModules.pushforward (𝟙 ((ringedSiteRingSheaf J 𝒪).over U))).Additive := sorry

/-- The functor on derived categories induced by extension by zero from the localized ringed site.
-/
noncomputable abbrev ringedSiteLocalizedExtensionByZeroDerived :
    DModU ⥤ DMod :=
  (SheafOfModules.pullback (𝟙 ((ringedSiteRingSheaf J 𝒪).over U))).mapDerivedCategory

/-- The functor on derived categories induced by restriction to the localized ringed site. -/
noncomputable abbrev ringedSiteLocalizedRestrictionDerived :
    DMod ⥤ DModU :=
  (SheafOfModules.pushforward (𝟙 ((ringedSiteRingSheaf J 𝒪).over U))).mapDerivedCategory

-- Proof sketch: apply the module-sheaf adjunction of Lemma `18.19.2` on complexes and combine it
-- with the K-injective comparison from Lemma `21.20.1`, exactly as in the textbook proof, to
-- obtain the derived Hom-adjunction.
/-- Lemma 21.20.8: for a ringed site `(\mathcal C, \mathcal O)` and `U : \mathcal C`, the
restriction functor `D(\mathcal O) ⥤ D(\mathcal O_U)` is a right adjoint; its intended left
adjoint is the derived extension-by-zero functor from `(\mathcal C/U, \mathcal O_U)` to
`(\mathcal C, \mathcal O)`. -/
instance ringedSiteLocalizedRestrictionDerived_isRightAdjoint :
    (ringedSiteLocalizedRestrictionDerived J 𝒪 U).IsRightAdjoint := sorry

-- Proof sketch: use the same derived adjunction construction as in
-- `ringedSiteLocalizedRestrictionDerived_isRightAdjoint`, but record the adjunction on the left
-- adjoint side.
/-- The derived extension-by-zero functor from the localized ringed site is a left adjoint. -/
instance ringedSiteLocalizedExtensionByZeroDerived_isLeftAdjoint :
    (ringedSiteLocalizedExtensionByZeroDerived J 𝒪 U).IsLeftAdjoint := sorry

end
