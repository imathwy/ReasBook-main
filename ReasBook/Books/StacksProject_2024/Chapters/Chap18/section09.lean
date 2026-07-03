import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_18_9_1 (from Chap18) -/
open CategoryTheory Opposite

universe v u

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ RingCat.{u})

/- Domain-style sampling for Definition 18.9.1:
- primary domain: presheaves of modules over a ring-valued presheaf on a category;
- sampled owner abstractions:
  `PresheafOfModules`,
  `PresheafOfModules.presheaf`,
  `PresheafOfModules.map_smul`,
  `PMod`;
- source-facing layer: the Stacks category `PMod(𝒪)` of presheaves of `𝒪`-modules on `C`;
- core/canonical owner: `PresheafOfModules 𝒪`;
- bridge/view layer: the existing project notation `PMod(𝒪)` from Definition `6.6.1`;
- primitive data versus derived API: `PresheafOfModules` already owns the objectwise module data
  and semilinear restriction maps as primitive fields, while the underlying presheaf of abelian
  groups and the morphism type are derived API.

This file should therefore reuse the existing canonical owner and source-facing notation rather
than keep a parallel local presentation of the same category.
-/

/- Definition 18.9.1: for a category `C` and a presheaf of rings `𝒪` on `C`, the category
`PMod(𝒪)` of presheaves of `𝒪`-modules is the canonical mathlib owner `PresheafOfModules 𝒪`. -/
recall PresheafOfModules

/- Source-facing bridge: the same category is written `PMod(𝒪)`. -/
#check PMod(𝒪)

variable (ℱ 𝒢 : PMod(𝒪))

/- Companion recall: a morphism of presheaves of `𝒪`-modules is a morphism in the category
`PMod(𝒪)`, i.e. an element of `ℱ ⟶ 𝒢`. -/
#check (ℱ ⟶ 𝒢)

/- Companion recall: a presheaf of `𝒪`-modules carries its underlying presheaf of abelian groups,
given by `PresheafOfModules.presheaf`. -/
recall PresheafOfModules.presheaf

/-! ### Lemma_18_9_2 (from Chap18) -/
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
