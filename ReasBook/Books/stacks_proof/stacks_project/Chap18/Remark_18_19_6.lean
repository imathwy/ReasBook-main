import Mathlib
import StacksProject_2024.Chap07.Lemma_7_22_2
import StacksProject_2024.Chap18.Lemma_18_19_2

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] [HasBinaryProducts C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/- Domain-style sampling for Remark 18.19.6:
- primary domain: extension by zero for sheaves of modules on a localized ringed site and the
  comparison with extension by zero on the underlying additive sheaves;
- sampled owner declarations:
  `ringedSiteLocalizedExtensionByZero`,
  `SheafOfModules.pullback`,
  `SheafOfModules.toSheaf`,
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`;
- best owner abstraction: the chapter owner `ringedSiteLocalizedExtensionByZero J 𝒪 U` for
  module-valued `j_{U!}`, together with the Chapter 7 sheaf owner obtained from
  `Over.forget U ⊣ Over.star U`;
- primitive data: the ringed site `((C, J), 𝒪)` and the object `U : C`;
- derived API: the comparison between module extension by zero and sheaf extension by zero after
  forgetting module structure.

Source/core/bridge triage:
- `source-facing`: extension by zero `j_{U!}` on `𝒪_U`-modules and on underlying abelian sheaves;
- `core/canonical`: `ringedSiteLocalizedExtensionByZero J 𝒪 U`,
  `SheafOfModules.pullback (𝟙 ((ringSheaf J 𝒪).over U))`, and the Chapter 7 comparison
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`;
- `bridge/view`: the underlying-sheaf comparison below. -/

/-- Helper for Remark 18.19.6: forgetting module structure after localized extension by zero is
definitionally the same as first forgetting and then applying additive-sheaf pushforward along
`Over.star U`. -/
private theorem ringedSiteLocalizedExtensionByZero_comp_toSheaf_eq :
    ringedSiteLocalizedExtensionByZero J 𝒪 U ⋙
        SheafOfModules.toSheaf (ringSheaf J 𝒪) =
      SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
        (Over.star U).sheafPushforwardContinuous AddCommGrpCat.{u} J (J.over U) := by
  -- Proof comment: unfolding the Chapter 18 owner leaves exactly the additive extension-by-zero
  -- functor on underlying sheaves.
  rfl

/-- Remark 18.19.6: after forgetting module structure, the localized extension-by-zero functor on
`𝒪_U`-modules is canonically isomorphic to the additive-sheaf pushforward along `Over.star U`,
i.e. the Chapter 7 sheaf-level `j_{U!}` owner before replacing it by the cocontinuous-site
formulation. -/
@[stacks 08P4]
noncomputable def ringedSiteLocalizedExtensionByZero_toSheaf :
    ringedSiteLocalizedExtensionByZero J 𝒪 U ⋙
        SheafOfModules.toSheaf (ringSheaf J 𝒪) ≅
      SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
        (Over.star U).sheafPushforwardContinuous AddCommGrpCat.{u} J (J.over U) :=
  -- Proof comment: package the functor-level definitional equality as the requested comparison
  -- isomorphism.
  eqToIso (ringedSiteLocalizedExtensionByZero_comp_toSheaf_eq J 𝒪 U)

section CocontinuousSheafOwner

variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify (J.over U) AddCommGrpCat.{u}]
variable [∀ P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u},
  (Over.forget U).op.HasPointwiseRightKanExtension P]

/- Companion bridge: the underlying additive-sheaf functor above is the canonical localization
extension-by-zero owner of Chapter 7, expressed as cocontinuous pushforward along `Over.forget U`.
-/
noncomputable abbrev ringedSiteLocalizedExtensionByZero_toCocontinuousSheafIso :
    ringedSiteLocalizedExtensionByZero J 𝒪 U ⋙
        SheafOfModules.toSheaf (ringSheaf J 𝒪) ≅
      SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
        (Over.forget U).sheafPushforwardCocontinuous AddCommGrpCat.{u} (J.over U) J :=
  ringedSiteLocalizedExtensionByZero_toSheaf J 𝒪 U ≪≫
    Functor.isoWhiskerLeft
      (SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)))
      (continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
        (Over.forget U) (Over.star U) AddCommGrpCat.{u} (Over.forgetAdjStar U))

end CocontinuousSheafOwner

end

end SheafOfModules.RingedSite
