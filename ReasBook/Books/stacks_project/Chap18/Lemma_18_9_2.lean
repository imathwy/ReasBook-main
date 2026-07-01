import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

variable {C : Type u} [Category.{u} C]
variable {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommRingCat.{u}}
variable (p : 𝒪₁ ⟶ 𝒪₂)

private abbrev ringPresheafHom :
    𝒪₁ ⋙ forget₂ CommRingCat RingCat ⟶ 𝒪₂ ⋙ forget₂ CommRingCat RingCat :=
  Functor.whiskerRight p (forget₂ CommRingCat RingCat)

private abbrev ringPresheafHomOverId :
    𝒪₁ ⋙ forget₂ CommRingCat RingCat ⟶ (𝟭 C).op ⋙ (𝒪₂ ⋙ forget₂ CommRingCat RingCat) :=
  ringPresheafHom p ≫ (𝒪₂ ⋙ forget₂ CommRingCat RingCat).leftUnitor.inv

/- Domain-style sampling for Lemma 18.9.2:
- primary domain: change of rings for presheaves of modules on a fixed base category;
- sampled owner API:
  `PresheafOfModules.pushforward`,
  `PresheafOfModules.pullback`,
  `PresheafOfModules.pullbackPushforwardAdjunction`,
  `SheafOfModules.pullbackPushforwardAdjunction`;
- best owner abstraction: `PresheafOfModules.pullbackPushforwardAdjunction` for the induced
  `RingCat`-valued morphism `ringPresheafHomOverId p`;
- primitive data: the change-of-rings morphism `p` of presheaves of commutative rings;
- same-site bridge: the induced `RingCat`-valued morphism `ringPresheafHom p`, together with the
  canonical identity-site transport `ringPresheafHomOverId p`;
- derived API: the Hom-set bijection in the statement of the lemma, obtained from the owner
  adjunction via `.homEquiv`.

Source/core/bridge triage:
- `source-facing`: the adjunction between change of rings and restriction of scalars on
  `PMod(𝒪₁)` and `PMod(𝒪₂)`;
- `core/canonical`: `PresheafOfModules.pullbackPushforwardAdjunction` for the induced ring-presheaf
  map;
- `bridge/view`: sectionwise module adjunctions such as
  `ModuleCat.extendRestrictScalarsAdj (p.app X).hom`.

This item should therefore recall the presheaf-level adjunction owner directly, not a sectionwise
specialization. -/

/- Lemma 18.9.2: for a morphism of presheaves of commutative rings `p : 𝒪₁ ⟶ 𝒪₂`, the
change-of-rings functor on presheaves of modules is left adjoint to restriction of scalars;
equivalently,
`Hom_{𝒪₁}(𝒢, ℱ_{𝒪₁}) ≃ Hom_{𝒪₂}(𝒪₂ ⊗_{p,𝒪₁} 𝒢, ℱ)`.
In canonical mathlib form this is the adjunction `PresheafOfModules.pullback ⊣
PresheafOfModules.pushforward` attached to the induced `RingCat`-valued morphism of presheaves. -/
#check
  (PresheafOfModules.pullbackPushforwardAdjunction (ringPresheafHomOverId p))
