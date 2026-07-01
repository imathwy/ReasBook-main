import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪₁ 𝒪₂ : Sheaf J RingCat.{u}}
variable (α : 𝒪₁ ⟶ 𝒪₂) (𝒢 : SheafOfModules 𝒪₁) (ℱ : SheafOfModules 𝒪₂)

private abbrev ringSheafHomOverId :
    𝒪₁ ⟶ ((𝟭 C).sheafPushforwardContinuous RingCat.{u} J J).obj 𝒪₂ :=
  α

/- Domain-style sampling for Lemma 18.11.3:
- primary domain: change of rings for sheaves of modules on one ringed site;
- sampled owner declarations:
  `SheafOfModules.restrictScalars`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`;
- best owner abstraction: `SheafOfModules.pullbackPushforwardAdjunction α`;
- primitive data: the ring-sheaf morphism `α : 𝒪₁ ⟶ 𝒪₂`;
- same-site bridge: the canonical identity-site transport `ringSheafHomOverId α`;
- derived API: the specialized Hom-set equivalence, where the same-site functor
  `SheafOfModules.pushforward (ringSheafHomOverId α)` is restriction of scalars.

Source/core/bridge triage:
- `source-facing`: the Hom-bijection for change of rings on one site;
- `core/canonical`: the adjunction
  `SheafOfModules.pullback (ringSheafHomOverId α) ⊣
    SheafOfModules.pushforward (ringSheafHomOverId α)`;
- `bridge/view`: the specialization of `.homEquiv` to `𝒢` and `ℱ`.

This file is therefore a bridge/view item, so the owner adjunction should be recalled directly and
the displayed Hom-bijection should stay a thin specialization. -/

/- Lemma 18.11.3, owner form: for sheaves of modules on a ringed site, extension of scalars along
`α : 𝒪₁ ⟶ 𝒪₂` is left adjoint to the same-site pushforward functor, i.e. to restriction of
scalars along `α`. -/
recall SheafOfModules.pullbackPushforwardAdjunction

/- Lemma 18.11.3: the adjunction for change of rings along `α : 𝒪₁ ⟶ 𝒪₂` induces the canonical
same-site Hom-set equivalence
`Hom_{𝒪₁}(𝒢, \mathrm{res}_α(ℱ)) ≃ Hom_{𝒪₂}(α^* 𝒢, ℱ)`,
where `α^*` is `SheafOfModules.pullback α` and the same-site `pushforward α` is restriction of
scalars. -/
#check
  ((SheafOfModules.pullbackPushforwardAdjunction (ringSheafHomOverId α)).homEquiv 𝒢 ℱ).symm
