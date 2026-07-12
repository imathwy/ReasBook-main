import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪₁ 𝒪₂ : Sheaf J CommRingCat.{max u v}}
variable (α : 𝒪₁ ⟶ 𝒪₂)

private abbrev ringSheaf (J : GrothendieckTopology C)
    (𝒪 : Sheaf J CommRingCat.{max u v}) : Sheaf J RingCat.{max u v} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

local notation "Mod(" 𝒪 ")" => SheafOfModules (ringSheaf J 𝒪)

variable (𝒢 : Mod(𝒪₁))
variable (ℱ : Mod(𝒪₂))

private abbrev sameSiteStructureMap (α : 𝒪₁ ⟶ 𝒪₂) :
    ringSheaf J 𝒪₁ ⟶ ((𝟭 C).sheafPushforwardContinuous RingCat.{max u v} J J).obj (ringSheaf J 𝒪₂) :=
  show ringSheaf J 𝒪₁ ⟶
      ((𝟭 C).sheafPushforwardContinuous RingCat.{max u v} J J).obj (ringSheaf J 𝒪₂) from
    (sheafCompose J (forget₂ CommRingCat RingCat)).map α

/- Domain-style sampling for Lemma 18.27.8:
- primary domain: same-site change of rings for sheaves of modules on a ringed site;
- sampled owner declarations:
  `sheafCompose`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`;
- best owner abstraction:
  `SheafOfModules.pullbackPushforwardAdjunction
    (sameSiteStructureMap α)`;
- primitive data: the same-site morphism of structure sheaves `α : 𝒪₁ ⟶ 𝒪₂`, an
  `𝒪₁`-module `𝒢`, and an `𝒪₂`-module `ℱ` in the canonical owner categories
  `SheafOfModules (ringSheaf J 𝒪₁)` and `SheafOfModules (ringSheaf J 𝒪₂)`;
- derived API: the specialized Hom-equivalence
  `((SheafOfModules.pullbackPushforwardAdjunction (sameSiteStructureMap α)).homEquiv 𝒢 ℱ).symm`.

Source/core/bridge triage:
- `source-facing`: the same-site change-of-rings Hom-bijection
  `Hom_{𝒪₁}(𝒢, \mathrm{res}_α(ℱ)) ≃ Hom_{𝒪₂}(α^*𝒢, ℱ)`;
- `core/canonical`: `SheafOfModules.pullbackPushforwardAdjunction
  (sameSiteStructureMap α)`;
- `bridge/view`: the private helper `sameSiteStructureMap α`, which packages the raw same-site ring
  map into the identity-site pushforward form required by the canonical adjunction owner.

Primitive-vs-derived split:
- primitive data: only `α`, `𝒢`, and `ℱ`;
- derived API: the textbook bijection. There is no new public owner here, because the adjunction is
  already owned canonically by `SheafOfModules.pullbackPushforwardAdjunction`.
-/

variable
  [(SheafOfModules.pushforward
      (sameSiteStructureMap α)).IsRightAdjoint]

/- Lemma 18.27.8, owner form: on a ringed site, extension of scalars along
`α : 𝒪₁ ⟶ 𝒪₂` is left adjoint to same-site restriction of scalars. In canonical form this is
exactly `SheafOfModules.pullbackPushforwardAdjunction
(sameSiteStructureMap α)`. -/
recall SheafOfModules.pullbackPushforwardAdjunction

/- Lemma 18.27.8 companion: the textbook Hom-set bijection is the inverse of the canonical
adjunction equivalence for the direct same-site ring-sheaf map induced by `α`. -/
#check
  (((SheafOfModules.pullbackPushforwardAdjunction
      (sameSiteStructureMap α)).homEquiv 𝒢 ℱ).symm :
    (𝒢 ⟶
      (SheafOfModules.pushforward
        (sameSiteStructureMap α)).obj ℱ) ≃
      ((SheafOfModules.pullback (sameSiteStructureMap α)).obj 𝒢 ⟶ ℱ))
