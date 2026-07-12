import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪₁ 𝒪₂ : Sheaf J RingCat.{max u v}}
variable (α : 𝒪₁ ⟶ 𝒪₂) (𝒢 : SheafOfModules 𝒪₁) (ℱ : SheafOfModules 𝒪₂)

private abbrev ringSheafHomOverId :
    𝒪₁ ⟶ ((𝟭 C).sheafPushforwardContinuous RingCat.{max u v} J J).obj 𝒪₂ :=
  α ≫ (Functor.sheafPushforwardContinuousId RingCat.{max u v} J).inv.app 𝒪₂

/- Domain-style sampling for Lemma 18.11.3:
- primary domain: change of rings for sheaves of modules on one ringed site;
- sampled owner declarations:
  `SheafOfModules.restrictScalars`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`;
- best owner abstraction:
  `SheafOfModules.pullbackPushforwardAdjunction (ringSheafHomOverId α)`;
- primitive data: the ring-sheaf morphism `α : 𝒪₁ ⟶ 𝒪₂`;
- same-site bridge: the identity-site recasting `ringSheafHomOverId α`, kept private because
  the owner adjunction is stated against the pushforward-over-identity shape;
- derived API: the specialized Hom-set equivalence, exposed on the source-facing right-hand side
  as `SheafOfModules.restrictScalars α` rather than as a parallel pushforward wrapper.

Source/core/bridge triage:
- `source-facing`: the Hom-bijection for change of rings on one site;
- `core/canonical`: the adjunction
  `SheafOfModules.pullback (ringSheafHomOverId α) ⊣
    SheafOfModules.pushforward (ringSheafHomOverId α)`;
- `bridge/view`: the private identity-site recasting `ringSheafHomOverId α` together with the
  specialization of `.homEquiv` to `𝒢` and `ℱ`.

This file is therefore a bridge/view item, so the owner adjunction should be recalled directly and
the displayed Hom-bijection should stay a thin specialization. -/

/- Lemma 18.11.3, owner form: for sheaves of modules on a ringed site, extension of scalars along
`α : 𝒪₁ ⟶ 𝒪₂`, encoded by the identity-site bridge `ringSheafHomOverId α`, is left adjoint to the
same-site pushforward functor, i.e. to restriction of scalars along `α`. -/
recall SheafOfModules.pullbackPushforwardAdjunction

/- Lemma 18.11.3: the adjunction for change of rings along `α : 𝒪₁ ⟶ 𝒪₂` induces the canonical
same-site Hom-set equivalence
`Hom_{𝒪₁}(𝒢, \mathrm{res}_α(ℱ)) ≃ Hom_{𝒪₂}(α^* 𝒢, ℱ)`,
where `α^*` is the same-site pullback
`SheafOfModules.pullback (ringSheafHomOverId α)` and the same-site pushforward is restriction of
scalars. -/
section

variable [(SheafOfModules.pushforward (ringSheafHomOverId α)).IsRightAdjoint]

#check
  (((SheafOfModules.pullbackPushforwardAdjunction (ringSheafHomOverId α)).homEquiv 𝒢 ℱ).symm :
    (𝒢 ⟶ (SheafOfModules.restrictScalars α).obj ℱ) ≃
      ((SheafOfModules.pullback (ringSheafHomOverId α)).obj 𝒢 ⟶ ℱ))

end
