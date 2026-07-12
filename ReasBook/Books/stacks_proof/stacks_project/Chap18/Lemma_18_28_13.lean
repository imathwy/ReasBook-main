import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.Lemma_18_39_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.RingedSite

/-
Domain-style sampling for Lemma 18.28.13:
- primary domain: change of rings for module sheaves on a ringed site and preservation of
  flatness under extension of scalars;
- sampled owner declarations:
  `ringSheaf`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.pullback`,
  `SheafOfModules.RingedSite.ringedSiteStructureMap`;
- best owner abstraction: the ambient owner is the flatness class
  `SheafOfModules.RingedSite.IsFlat`, and same-site extension of scalars is the canonical
  `SheafOfModules.pullback` applied to the public same-site bridge
  `ringedSiteStructureMap`;
- primitive data: a morphism `α : 𝒪₁ ⟶ 𝒪₂` of commutative structure sheaves and a module
  `𝒢 : SheafOfModules (ringSheaf J 𝒪₁)` with flatness instance;
- bridge/view owner: `ringedSiteStructureMap α`, the canonical identity-site morphism used by
  `SheafOfModules.pullback`.

Source/core/bridge triage:
- `source-facing`: extension of scalars along a morphism of structure sheaves on a fixed site;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat`, `ringSheaf`, and
  `SheafOfModules.pullback`;
- `bridge/view`: the same-site structure morphism `ringedSiteStructureMap α`.

This file should therefore reuse `IsFlat` and `SheafOfModules.pullback` directly, with the
same-site transport expressed through the public bridge owner `ringedSiteStructureMap`, rather
than through a duplicate local wrapper.
-/

variable {C : Type u} [Category.{u} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪₁ 𝒪₂ : Sheaf J CommRingCat.{u}}
variable (α : 𝒪₁ ⟶ 𝒪₂)

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

open scoped SheafOfModules.RingedSite

-- Proof sketch: the source-facing change-of-rings datum is the morphism
-- `α : 𝒪₁ ⟶ 𝒪₂` of commutative structure sheaves. The corresponding extension of scalars is the
-- canonical same-site pullback along the canonical structure morphism
-- `ringedSiteStructureMap α`, and
-- flatness is expressed through the chapter owner
-- `SheafOfModules.RingedSite.IsFlat`.
/-- Lemma 18.28.13: for a morphism of sheaves of commutative rings
`\mathcal O_1 \to \mathcal O_2` on a site, if `\mathcal G` is a flat
`\mathcal O_1`-module, then the extension of scalars
`\mathcal G \otimes_{\mathcal O_1} \mathcal O_2`, canonically realized as the same-site
change-of-rings pullback, is a flat `\mathcal O_2`-module. -/
@[stacks 05V4]
theorem pullback_isFlat_of_isFlat
    (𝒢 : SheafOfModules (ringSheaf J 𝒪₁))
    [MonoidalCategory (Mod(𝒪₁))]
    [MonoidalCategory (Mod(𝒪₂))]
    [IsFlat 𝒪₁ 𝒢] :
    IsFlat 𝒪₂ ((SheafOfModules.pullback
      (SheafOfModules.RingedSite.ringedSiteStructureMap α)).obj 𝒢) := by
  let φ : 𝒪₁ ⟶ ((𝟭 C).sheafPushforwardContinuous CommRingCat.{u} J J).obj 𝒪₂ :=
    α ≫ (Functor.sheafPushforwardContinuousId CommRingCat.{u} J).inv.app 𝒪₂
  -- Proof comment: specialize the already-proved site-level pullback-flatness theorem to the
  -- identity functor on `C`; its underlying structure morphism is exactly `ringedSiteStructureMap`.
  simpa [φ, RingedSite.ringedSiteUnderlyingStructureMap,
    SheafOfModules.RingedSite.ringedSiteStructureMap] using
    (_root_.pullback_isFlat_of_isFlat
      (F := 𝟭 C) (φ := φ) (ℱ := 𝒢))

end SheafOfModules.RingedSite
