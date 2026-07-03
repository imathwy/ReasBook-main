import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_18_13_1 (from Chap18) -/
/- Definition 18.13.1 (1): for a morphism of ringed topoi or ringed sites, the direct image of a
sheaf of modules is the canonical functor `SheafOfModules.pushforward`, whose underlying sheaf of
abelian groups is the usual pushforward and whose module structure is obtained by restricting
scalars along the structure-sheaf map `f^\sharp : \mathcal O_{\mathcal D} \to f_* \mathcal
O_{\mathcal C}`. -/
recall SheafOfModules.pushforward

/- Definition 18.13.1 (2): for a morphism of ringed topoi or ringed sites, the inverse image of a
sheaf of modules is the canonical functor `SheafOfModules.pullback`, i.e. the sheaf
`\mathcal O_{\mathcal C} \otimes_{f^{-1}\mathcal O_{\mathcal D}} f^{-1}\mathcal G` with its
canonical `\mathcal O_{\mathcal C}`-module structure. -/
recall SheafOfModules.pullback

/-! ### Lemma_18_13_2 (from Chap18) -/
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

/-! ### Lemma_18_13_3 (from Chap18) -/
open CategoryTheory SheafOfModules

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃ u

/- Domain-style sampling for Lemma 18.13.3:
- primary domain: pseudofunctoriality of pushforward and pullback for sheaves of modules on
  ringed sites/topoi;
- sampled owner declarations:
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforwardComp`,
  `SheafOfModules.pullbackComp`;
- owner abstraction: the canonical owners are `SheafOfModules.pushforwardComp` and
  `SheafOfModules.pullbackComp`;
- primitive data: composable morphisms of sheaves of rings on sites, encoded by `φ` and `ψ`;
- derived API: the canonical comparison isomorphisms for composition.

Source/core/bridge triage:
- `source-facing`: the comparison between the functor attached to a composite and the composite of
  the corresponding functors;
- `core/canonical`: `SheafOfModules.pushforwardComp` and `SheafOfModules.pullbackComp`;
- `bridge/view`: only the symmetric orientation used below so the public surface matches the
  textbook phrasing exactly.

No local wrapper belongs here: the file should reuse the owner declarations directly. -/

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {K' : GrothendieckTopology D'}
  {F : C ⥤ D} {G : D ⥤ D'}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} {R' : Sheaf K' RingCat.{u}}
  [Functor.IsContinuous F J K] [Functor.IsContinuous G K K']
  [Functor.IsContinuous (F ⋙ G) J K']
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R')

/- Lemma 18.13.3 (1): for composable morphisms of ringed topoi, the direct-image functor attached
to the composite is canonically isomorphic to the composite of the direct-image functors. -/
#check ((pushforwardComp φ ψ).symm :
  pushforward
      ((φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) :
        S ⟶ ((F ⋙ G).sheafPushforwardContinuous RingCat.{u} J K').obj R') ≅
    pushforward ψ ⋙ pushforward φ)

variable [(pushforward φ).IsRightAdjoint] [(pushforward ψ).IsRightAdjoint]

/- Lemma 18.13.3 (2): for composable morphisms of ringed topoi, the inverse-image functor attached
to the composite is canonically isomorphic to the composite of the inverse-image functors. -/
#check ((pullbackComp φ ψ).symm :
  pullback
      ((φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) :
        S ⟶ ((F ⋙ G).sheafPushforwardContinuous RingCat.{u} J K').obj R') ≅
    pullback φ ⋙ pullback ψ)

end
