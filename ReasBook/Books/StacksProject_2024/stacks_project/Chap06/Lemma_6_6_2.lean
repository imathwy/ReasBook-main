import Mathlib
import Mathlib.Tactic.Recall

open CategoryTheory TopologicalSpace

noncomputable section

namespace TopCat.Presheaf

universe u

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : X.Presheaf RingCat.{u}} (p : 𝒪₁ ⟶ 𝒪₂)
variable (𝒢 : PresheafOfModules 𝒪₁) (ℱ : PresheafOfModules 𝒪₂)

private abbrev ringPresheafHomOverId :
    𝒪₁ ⟶ (𝟭 (Opens X)).op ⋙ 𝒪₂ :=
  p ≫ 𝒪₂.leftUnitor.inv

/- Domain-style sampling for Lemma 6.6.2:
- primary domain: change of rings for presheaves of modules, expressed by the pullback-pushforward
  adjunction over a morphism of presheaves of rings on `X`;
- sampled owner API:
  `PresheafOfModules.pullbackPushforwardAdjunction`,
  `PresheafOfModules.pullback`,
  `PresheafOfModules.pushforward`,
  `Equiv.bijective`;
- best owner abstraction: the canonical adjunction
  `PresheafOfModules.pullbackPushforwardAdjunction (ringPresheafHomOverId p)`;
- primitive data: the ring-map `p : 𝒪₁ ⟶ 𝒪₂` and the module presheaves `𝒢`, `ℱ`;
- bridge/view: the same-site ring-map `p` viewed in the identity-on-opens shape required by the
  owner, namely `ringPresheafHomOverId p : 𝒪₁ ⟶ (𝟭 (Opens X)).op ⋙ 𝒪₂`;
- derived API: the hom-equivalence
  `((PresheafOfModules.pullbackPushforwardAdjunction (ringPresheafHomOverId p)).homEquiv 𝒢 ℱ)`
  and the source-facing bijectivity statement, which is exactly its inverse equivalence's
  canonical theorem `.bijective`.

Source/core/bridge triage:
- `source-facing`: the Stacks bijection on morphisms for change of rings;
- `core/canonical`: `PresheafOfModules.pullbackPushforwardAdjunction (ringPresheafHomOverId p)`;
- `bridge/view`: the identity-on-opens transport `ringPresheafHomOverId p`.
-/

/- Lemma 6.6.2: for presheaves of modules on a topological space `X`, change of rings along
`p : 𝒪₁ ⟶ 𝒪₂` is left adjoint to restriction of scalars. This is exactly the canonical
adjunction `PresheafOfModules.pullbackPushforwardAdjunction`, specialized to the identity functor
on `Opens X`. -/
recall PresheafOfModules.pullbackPushforwardAdjunction

/- Lemma 6.6.2 companion: the source bijection on morphisms is exactly the canonical theorem that
the inverse of the change-of-rings hom-equivalence is bijective. -/
#check
  Equiv.bijective
    (((PresheafOfModules.pullbackPushforwardAdjunction (ringPresheafHomOverId p)).homEquiv 𝒢 ℱ).symm)

end TopCat.Presheaf
