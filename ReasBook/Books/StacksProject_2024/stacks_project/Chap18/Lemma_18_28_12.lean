import Mathlib
import StacksProject_2024.stacks_project.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

namespace SheafOfModules.RingedSite
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling for Lemma 18.28.12:
- primary domain: flat sheaves of modules on a ringed site, with the tensor product acting by the
  chapter owner functor on `Mod(\mathcal O)`;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.IsFlat`,
  `moduleTensor`,
  `tensorRight`,
  `tensorRightTensor`,
  `exactFunctor`;
- best owner abstraction: the flatness owner is `SheafOfModules.RingedSite.IsFlat`, and the
  tensor owner is `moduleTensor` with source-facing notation `⊗` on the chapter owner category
  `ringedSiteModuleCategory J 𝒪`;
- primitive data: two modules `𝒢 𝓕 : ringedSiteModuleCategory J 𝒪`;
- derived API: the flatness instance/theorem for the source-facing tensor product `𝒢 ⊗ 𝓕`.

Source/core/bridge triage:
- `source-facing`: flatness of the tensor product of two flat `\mathcal O`-modules;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`, `IsFlat`, `moduleTensor`, and
  `tensorRight`;
- `bridge/view`: the exactness witness `IsFlat.exact_tensor` and the canonical comparison
  `tensorRightTensor`, both used only in the proof.

This file should therefore keep the source-facing tensor statement and reuse the chapter flatness
owner directly, without introducing any parallel flatness wrapper. -/

-- Proof sketch: flatness is owned by the exact tensor functor
-- `SheafOfModules.RingedSite.IsFlat`. Tensoring with `𝒢 ⊗ 𝓕` is canonically
-- isomorphic to the
-- composite `tensorRight 𝒢 ⋙ tensorRight 𝓕`, so exactness follows from exactness of the two
-- flat tensor functors, stability of exactness under composition, and transport across that
-- comparison isomorphism.
instance (𝒢 𝓕 : Mod) [MonoidalCategory Mod] [h𝒢 : IsFlat 𝒪 𝒢] [h𝓕 : IsFlat 𝒪 𝓕] :
    IsFlat 𝒪 (𝒢 ⊗ 𝓕) := by
  let h𝓕' : Mod ⥤ₑ Mod := ⟨MonoidalCategory.tensorRight 𝓕, h𝓕.exact_tensor⟩
  let h𝒢' : Mod ⥤ₑ Mod := ⟨MonoidalCategory.tensorRight 𝒢, h𝒢.exact_tensor⟩
  refine ⟨?_⟩
  have hcomp :
      exactFunctor Mod Mod
        (MonoidalCategory.tensorRight 𝒢 ⋙ MonoidalCategory.tensorRight 𝓕) :=
    (((ExactFunctor.whiskeringRight Mod Mod Mod).obj h𝓕').obj h𝒢').property
  exact ObjectProperty.prop_of_iso
    (exactFunctor Mod Mod) (MonoidalCategory.tensorRightTensor 𝒢 𝓕).symm hcomp

/-- Lemma 18.28.12: for a ringed site `(\mathcal C, \mathcal O)`, if `\mathcal G` and
`\mathcal F` are flat `\mathcal O`-modules, then their tensor product
`\mathcal G \otimes_\mathcal O \mathcal F`, formalized here as `𝒢 ⊗ 𝓕`, is again a flat
`\mathcal O`-module. -/
theorem isFlat_tensor
    (𝒢 𝓕 : Mod)
    [MonoidalCategory Mod]
    [IsFlat 𝒪 𝒢] [IsFlat 𝒪 𝓕] :
    IsFlat 𝒪 (𝒢 ⊗ 𝓕) :=
  inferInstance

end SheafOfModules.RingedSite
