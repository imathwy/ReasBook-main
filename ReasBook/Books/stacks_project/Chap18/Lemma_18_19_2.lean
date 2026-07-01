import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on a ringed
site. -/
abbrev ringedSiteModuleCategory {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

section

variable {C : Type u} [Category.{u} C] [CategoryTheory.Limits.HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/- Domain-style sampling for Lemma 18.19.2:
- primary domain: pullback/pushforward of sheaves of modules on localized ringed sites;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  the presheaf analogue `PresheafOfModules.pullbackPushforwardAdjunction` from Remark `18.19.7`;
- best owner abstraction:
  `SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`;
- primitive data: the ringed site `(\mathcal C, J, \mathcal O)` and the object `U : C`;
- derived API: any localized restriction/extension-by-zero functor expression and the Hom-set
  bijection obtained from `.homEquiv`.

Source/core/bridge triage:
- `source-facing`: the adjunction `j_{U!} ⊣ j_U^*` on the localized ringed site;
- `core/canonical`: the specialized owner adjunction below;
- `bridge/view`: any later use of `.homEquiv`, exactness, or derived-category consequences.

This file keeps only the reusable owner alias `ringedSiteModuleCategory`. The localized functors
themselves are used through the canonical `SheafOfModules.pullback` / `SheafOfModules.pushforward`
API rather than through parallel public wrappers. -/

/- Lemma 18.19.2: on the localized ringed site `(C/U, J.over U, \mathcal O_U)`, extension by
zero is left adjoint to restriction. In Lean this is exactly the specialized owner adjunction
`SheafOfModules.pullbackPushforwardAdjunction` for the identity morphism of the localized
structure sheaf `\mathcal O_U = \mathcal O.over U`. -/
#check
  (SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U)))

end
