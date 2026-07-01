import Mathlib
import stacks_project.Chap18.Definition_18_28_1
import stacks_project.Chap21.Definition_21_17_14

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling for Lemma 21.17.15:
- primary domain: flat sheaves of modules on a ringed site and the first left-derived tensor
  functor on the ambient monoidal abelian category `Mod`;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.IsFlat`,
  `CategoryTheory.Tor`,
  `Definition_21_17_14`'s chapter-21 specialization `Tor Mod p`;
- best owner abstraction: flatness is already owned by `SheafOfModules.RingedSite.IsFlat`, while
  the Tor side of the criterion is already owned by the canonical bifunctor `Tor Mod 1`; this item
  should stay a source-facing criterion theorem and reuse that owner directly;
- primitive data: the module `ℱ : Mod`;
- derived API: the vanishing condition `∀ 𝒢 : Mod, IsZero (((Tor Mod 1).obj ℱ).obj 𝒢)`.

Source/core/bridge triage:
- `source-facing`: the flatness criterion stated as vanishing of `Tor₁`;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat` and `Tor Mod 1`;
- `bridge/view`: no extra bridge is needed here, because Definition `21.17.14` already records the
  ringed-site specialization of the canonical Tor owner. -/

variable [MonoidalCategory Mod]
variable [MonoidalPreadditive Mod]
variable [HasProjectiveResolutions Mod]

-- Proof sketch: if `ℱ` is flat, then tensoring with `ℱ` is exact, so its first left derived
-- functor vanishes and hence `Tor₁` is zero against every `𝒢`. Conversely, apply the long exact
-- `Tor` sequence to a short exact sequence `0 ⟶ 𝒢 ⟶ ℋ ⟶ 𝒬 ⟶ 0`; vanishing of `Tor₁(ℱ, 𝒬)` forces
-- tensoring with `ℱ` to preserve monomorphisms, which is the flatness criterion.
/-- Lemma 21.17.15: a sheaf of `\mathcal O`-modules on a ringed site is flat if and only if
`\operatorname{Tor}_1^\mathcal O(\mathcal F, \mathcal G)` vanishes for every
`\mathcal O`-module `\mathcal G`. -/
theorem isFlat_iff_isZero_tor_one
    (ℱ : Mod) :
    IsFlat 𝒪 ℱ ↔
      ∀ 𝒢 : Mod, IsZero (((Tor Mod 1).obj ℱ).obj 𝒢) := sorry

end SheafOfModules.RingedSite
