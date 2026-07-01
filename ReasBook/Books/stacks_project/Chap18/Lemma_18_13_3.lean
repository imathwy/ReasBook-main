import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
