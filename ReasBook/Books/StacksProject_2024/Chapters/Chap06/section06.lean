import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_6_1 (from Chap06) -/
notation:max "PMod(" 𝒪 ")" => PresheafOfModules 𝒪

open CategoryTheory

universe u

variable {X : TopCat.{u}}
variable (𝒪 : X.Presheaf RingCat.{u})

/- Domain-style sampling for Definition 6.6.1:
- primary domain: presheaves of modules over a ring-valued presheaf on a topological space;
- sampled owner abstractions:
  `PresheafOfModules`,
  `PresheafOfModules.presheaf`,
  `PresheafOfModules.map_smul`,
  `SheafOfModules`;
- source-facing layer: the Stacks category `PMod(𝒪)` of presheaves of `𝒪`-modules on `X`;
- core/canonical owner: `PresheafOfModules 𝒪`;
- bridge/view layer: the notation `PMod(𝒪)` on top of the canonical owner
  `PresheafOfModules 𝒪`;
- primitive data versus derived API: `PresheafOfModules` already owns the module objects and
  semilinear restriction maps as primitive data, while the underlying presheaf of abelian groups
  and the semilinearity lemma are derived API. This file should therefore recall the canonical
  owner directly and expose the source-facing notation `PMod(𝒪)`, rather than introduce a local
  alias or wrapper.
-/

/- Definition 6.6.1 (Tag 006P): for a presheaf of rings `𝒪` on a topological space `X`, the
Stacks Project category `PMod(𝒪)` of presheaves of `𝒪`-modules with `𝒪`-linear morphisms is the
canonical mathlib category `PresheafOfModules 𝒪`. -/
recall PresheafOfModules

/- Source-facing bridge: Stacks writes the same category as `PMod(𝒪)`. -/
#check PMod(𝒪)

variable (ℱ 𝒢 : PMod(𝒪))

/- Companion recall: morphisms in `PMod(𝒪)` are precisely the morphisms in the canonical category
`PresheafOfModules 𝒪`. -/
#check (ℱ ⟶ 𝒢)

/- Companion recall: a presheaf of `𝒪`-modules carries its canonical underlying presheaf of
abelian groups, given by `PresheafOfModules.presheaf`. -/
recall PresheafOfModules.presheaf

/- Companion recall: the restriction maps in a presheaf of `𝒪`-modules are semilinear. -/
recall PresheafOfModules.map_smul

/-! ### Lemma_6_6_2 (from Chap06) -/
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
