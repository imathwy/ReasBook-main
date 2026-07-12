import StacksProject_2024.Chap20.RingedSpaceOpensModuleCategory
import StacksProject_2024.Chap21.Definition_21_17_14

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped RingedSiteTor

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasProjectiveResolutions (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 20.26.16:
- primary domain: flat sheaves of modules on a ringed space and the first left-derived tensor
  functor on the ambient monoidal abelian category `ModX`;
- sampled owner declarations:
  `SheafOfModules.IsFlat`,
  `SheafOfModules.isFlat_iff_ringedSite_isFlat`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.RingedSite.isFlat_iff_isZero_tor_one`,
  `Tor[1](ℱ, 𝒢)`;
- best owner abstraction: for ringed spaces the repository's source-facing flatness owner is
  `SheafOfModules.IsFlat`; the Chapter 21 Tor-flatness criterion remains the core theorem, and
  Chapter 18 supplies the canonical bridge `SheafOfModules.isFlat_iff_ringedSite_isFlat`;
- primitive data: the module sheaf `ℱ : ModX`;
- derived API: the source-facing ringed-space criterion
  `∀ 𝒢 : ModX, IsZero (Tor[1](ℱ, 𝒢))`.

Source/core/bridge triage:
- `source-facing`: the ringed-space Tor-vanishing criterion below, stated with
  `SheafOfModules.IsFlat`;
- `core/canonical`: `SheafOfModules.RingedSite.isFlat_iff_isZero_tor_one`;
- `bridge/view`: `SheafOfModules.isFlat_iff_ringedSite_isFlat`. -/

/-- Lemma 20.26.16: an `𝒪_X`-module `ℱ` on a ringed space `(X, 𝒪_X)` is flat if and only if
`Tor[1](ℱ, 𝒢)` vanishes for every `𝒪_X`-module `𝒢`. -/
@[stacks 08BQ]
theorem isFlat_iff_isZero_tor_one
    (ℱ : ModX) :
    ℱ.IsFlat ↔ ∀ 𝒢 : ModX, IsZero (Tor[1](ℱ, 𝒢)) := by
  sorry

/-- Forward companion to Lemma 20.26.16: flat `𝒪_X`-modules have vanishing first Tor against
every `𝒪_X`-module. -/
theorem isZero_tor_one_of_isFlat
    (ℱ : ModX) (hFlat : ℱ.IsFlat) (𝒢 : ModX) :
    IsZero (Tor[1](ℱ, 𝒢)) :=
  (isFlat_iff_isZero_tor_one ℱ).1 hFlat 𝒢

/-- Typeclass form of the forward direction of Lemma 20.26.16: if `ℱ` is flat, then
`Tor[1](ℱ, 𝒢)` is zero for every `𝒪_X`-module `𝒢`. -/
instance instIsZeroTorOneOfIsFlat
    (ℱ 𝒢 : ModX) [hFlat : ℱ.IsFlat] :
    IsZero (Tor[1](ℱ, 𝒢)) :=
  isZero_tor_one_of_isFlat ℱ hFlat 𝒢

/-- Converse companion to Lemma 20.26.16: vanishing of first Tor against every `𝒪_X`-module
detects flatness. -/
theorem isFlat_of_isZero_tor_one
    (ℱ : ModX) (hTor : ∀ 𝒢 : ModX, IsZero (Tor[1](ℱ, 𝒢))) :
    ℱ.IsFlat :=
  (isFlat_iff_isZero_tor_one ℱ).2 hTor

end AlgebraicGeometry.RingedSpace
