import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

/-- The underlying `RingCat`-valued structure map attached to a morphism of sheaves of
commutative rings on a fixed site. -/
abbrev ringedSiteStructureMap
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : Sheaf J CommRingCat.{max u v}}
    (α : 𝒪₁ ⟶ 𝒪₂) :
    ringSheaf J 𝒪₁ ⟶
      ((𝟭 C).sheafPushforwardContinuous RingCat.{max u v} J J).obj (ringSheaf J 𝒪₂) :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map α

/-
Domain-style sampling for Lemma 18.28.13:
- primary domain: change of rings for module sheaves on a ringed site and preservation of
  flatness under extension of scalars;
- sampled owner declarations:
  `ringSheaf`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.pullback`,
  `ringedSiteStructureMap`;
- best owner abstraction: the ambient owner is the flatness class
  `SheafOfModules.RingedSite.IsFlat`, and same-site extension of scalars is the canonical
  `SheafOfModules.pullback` applied to the public same-site bridge
  `ringedSiteStructureMap`;
- primitive data: a morphism `α : 𝒪₁ ⟶ 𝒪₂` of commutative structure sheaves and a module
  `𝒢 : SheafOfModules (ringSheaf J 𝒪₁)` with flatness instance;
- bridge/view owner: `ringedSiteStructureMap α`, which packages the identity-site transport
  needed by `SheafOfModules.pullback`.

Source/core/bridge triage:
- `source-facing`: extension of scalars along a morphism of structure sheaves on a fixed site;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat`, `ringSheaf`, and
  `SheafOfModules.pullback`;
- `bridge/view`: the underlying `RingCat`-valued same-site structure map
  `ringedSiteStructureMap α`.

This file should therefore reuse `IsFlat` and `SheafOfModules.pullback` directly, with the
same-site transport expressed through the public bridge owner `ringedSiteStructureMap`, rather
than through an inaccessible local wrapper.
-/

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪₁ 𝒪₂ : Sheaf J CommRingCat.{max u v}}
variable (α : 𝒪₁ ⟶ 𝒪₂)
variable [(PresheafOfModules.pushforward (ringedSiteStructureMap α).hom).IsRightAdjoint]
variable [(SheafOfModules.pushforward (ringedSiteStructureMap α)).IsRightAdjoint]

-- Proof sketch: the source-facing change-of-rings datum is the morphism
-- `α : 𝒪₁ ⟶ 𝒪₂` of commutative structure sheaves. The corresponding extension of scalars is the
-- canonical same-site pullback along the induced `RingCat`-valued structure map
-- `ringedSiteStructureMap α`, and flatness is expressed through the chapter owner
-- `SheafOfModules.RingedSite.IsFlat`.
/-- Lemma 18.28.13: for a morphism of sheaves of commutative rings
`\mathcal O_1 \to \mathcal O_2` on a site, if `\mathcal G` is a flat
`\mathcal O_1`-module, then the extension of scalars
`\mathcal G \otimes_{\mathcal O_1} \mathcal O_2`, canonically realized as the same-site
change-of-rings pullback, is a flat `\mathcal O_2`-module. -/
theorem pullback_isFlat
    (𝒢 : SheafOfModules (ringSheaf J 𝒪₁))
    [IsFlat 𝒪₁ 𝒢] :
    IsFlat 𝒪₂ ((SheafOfModules.pullback (ringedSiteStructureMap α)).obj 𝒢) := sorry

end SheafOfModules.RingedSite
