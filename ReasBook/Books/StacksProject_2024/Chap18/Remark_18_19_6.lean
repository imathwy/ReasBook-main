import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap18.Lemma_18_27_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C]

private abbrev localizedStructureMap (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat.{u}) (U : C) :
    Sheaf (J.over U) RingCat.{u} :=
  (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U)

/- Domain-style sampling for Remark 18.19.6:
- primary domain: localized extension-by-zero for sheaves of modules on a ringed site, and its
  compatibility with passage to the underlying sheaf of abelian groups;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.toSheaf`,
  `SheafOfModules.sheafificationCompPullback`,
  `(Over.forget U).sheafPushforwardContinuous`;
- best owner abstraction: the canonical lower-shriek owner
  `SheafOfModules.pullback
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`
  together with the canonical pullback/sheafification comparison
  `SheafOfModules.sheafificationCompPullback
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`;
- primitive data: the ringed site `(\mathcal C, J, \mathcal O)` and the object `U : C`;
- derived API: the restriction-side definitional equality with `toSheaf`.

Source/core/bridge triage:
- `source-facing`: the `j_{U!}` square saying that extension by zero on `\mathcal O_U`-modules is
  compatible with forgetting to the underlying abelian sheaf;
- `core/canonical`: `SheafOfModules.pullback
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`,
  `SheafOfModules.sheafificationCompPullback
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`,
  `SheafOfModules.pushforward
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`, and
  `(Over.forget U).sheafPushforwardContinuous AddCommGrpCat (J.over U) J`;
- `bridge/view`: the restriction-side equality below, which is the right-adjoint mate of the
  source-facing left-adjoint square.

This remark therefore should present the lower-shriek square through the upstream owner
`SheafOfModules.sheafificationCompPullback`, specialized to the identity map of `\mathcal O_U`,
and keep the restriction compatibility only as a companion. -/

section ExtensionByZeroSide

variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/- Remark 18.19.6: the extension-by-zero square for `j_{U!}` on sheaves of modules is exactly the
canonical pullback/sheafification comparison specialized to the identity morphism of
`\mathcal O_U`; equivalently, localized extension by zero commutes with forgetting to the
underlying sheaf of abelian groups. -/
recall SheafOfModules.sheafificationCompPullback

-- Proof sketch: the upstream owner
-- `SheafOfModules.sheafificationCompPullback
--   (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`
-- identifies module-valued extension by zero with presheaf extension by zero followed by
-- sheafification. Forgetting module structure turns that presheaf pullback into the abelian lower
-- shriek along `Over.forget U`, yielding the source-facing `j_{U!}` square.
/- Applying the recalled natural isomorphism above to an `\mathcal O_U`-module `\mathcal F`
recovers the source-facing comparison
`(j_{U!}\mathcal F)_{\mathrm{ab}} \cong j_{U!}(\mathcal F_{\mathrm{ab}})`.
We keep `SheafOfModules.sheafificationCompPullback` itself as the public entry, rather than a
parallel objectwise wrapper. -/

end ExtensionByZeroSide

section RestrictionSide

variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

-- Proof sketch: localized restriction is `SheafOfModules.pushforward` for the identity map on
-- `\mathcal O_U`. Forgetting module structure turns this pushforward into the usual sheaf
-- pushforward along `Over.forget U`, so the two composites are definitionally equal.
/-- Companion to Remark 18.19.6: localized restriction commutes definitionally with forgetting to
the underlying sheaf of abelian groups. This is the right-adjoint mate of the main
extension-by-zero square above. -/
theorem ringedSiteLocalizedRestriction_toSheaf :
    SheafOfModules.pushforward (𝟙 (localizedStructureMap J 𝒪 U)) ⋙
        SheafOfModules.toSheaf (localizedStructureMap J 𝒪 U) =
      SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪) ⋙
        (Over.forget U).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over U) J :=
  rfl

end RestrictionSide

end SheafOfModules.RingedSite
