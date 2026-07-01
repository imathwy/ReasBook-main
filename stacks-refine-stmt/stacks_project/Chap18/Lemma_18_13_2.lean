import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u₁ u₂ v₁ v₂ u

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {F : C ⥤ D} [Functor.IsContinuous F J K]
variable {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
variable (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
variable [(SheafOfModules.pushforward φ).IsRightAdjoint]
variable (ℱ : SheafOfModules S) (𝒢 : SheafOfModules R)

/- Domain-style sampling for Lemma 18.13.2:
- primary domain: pullback/pushforward of sheaves of modules along a morphism of ringed sites or
  ringed topoi;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `Adjunction.homEquiv`;
- best owner abstraction: the adjunction
  `SheafOfModules.pullbackPushforwardAdjunction φ`;
- primitive data: the structure-sheaf morphism `φ`, with the induced right-adjoint structure on
  `SheafOfModules.pushforward φ` supplied canonically in the ringed-site/ringed-topos situations
  covered by the source;
- derived API: the source Hom-set bijection obtained from that adjunction via `.homEquiv`.

Source/core/bridge triage:
- `source-facing`: the statement that `f^*` is left adjoint to `f_*`, equivalently the canonical
  bijection
  `Hom((SheafOfModules.pullback φ).obj ℱ, 𝒢) ≃
    Hom(ℱ, (SheafOfModules.pushforward φ).obj 𝒢)`;
- `core/canonical`: `SheafOfModules.pullbackPushforwardAdjunction φ`;
- `bridge/view`: the specialization of its `homEquiv` to `ℱ` and `𝒢`.

This file therefore keeps the main item as a direct recall of the owner adjunction and exposes the
textbook Hom-bijection only through the canonical derived API, with no parallel local wrapper.
-/

/- Lemma 18.13.2: for a morphism of ringed topoi or ringed sites, the inverse-image functor
`f^*` on sheaves of modules is left adjoint to the direct-image functor `f_*`. In canonical
mathlib form this is exactly `SheafOfModules.pullbackPushforwardAdjunction φ`. -/
recall SheafOfModules.pullbackPushforwardAdjunction

/- Lemma 18.13.2 companion: the textbook Hom-set bijection is the specialized adjunction
equivalence coming from `SheafOfModules.pullbackPushforwardAdjunction φ`. -/
#check ((SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv ℱ 𝒢 :
  (((SheafOfModules.pullback φ).obj ℱ) ⟶ 𝒢) ≃
    (ℱ ⟶ (SheafOfModules.pushforward φ).obj 𝒢))
