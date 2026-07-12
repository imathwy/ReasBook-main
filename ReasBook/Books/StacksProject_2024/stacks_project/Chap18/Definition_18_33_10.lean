import Mathlib
import StacksProject_2024.Chap18.Definition_18_31_1
import StacksProject_2024.Chap18.Lemma_18_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite
open scoped RelativeDerivation RingedSite.Hom

noncomputable section

universe u

namespace RingedSite.Hom

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}

local notation "X" => RingedSite.ofCommRingSheaf JC 𝒪
local notation "Y" => RingedSite.ofCommRingSheaf JD 𝒪'

/- Domain-style sampling for Definition 18.33.10:
- primary domain: relative differentials for a morphism of ringed topoi presented by a bundled
  morphism of ringed sites;
- sampled owner declarations:
  `RingedSite.Hom.inverseImageStructureSheafMap`,
  `SheafOfModules.RingedSite.relativeDifferentials`,
  `SheafOfModules.RingedSite.relativeDifferential`,
  `SheafOfModules.RingedSite.relativeDifferentials_representsDerivations`;
- best owner abstraction: the bundled morphism `f : X ⟶ Y`, with source-facing surface `Ω[f]`
  and `d[f]`;
- primitive data in this file: no new primitive data beyond the established bridge
  `inverseImageStructureSheafMap f : f⁻¹𝒪_Y ⟶ 𝒪_X`;
- derived API: only the source-facing notation `Ω[f]` and `d[f]`; the relative derivation type
  already has the canonical generic-site owner `Der[φ ; F]`.

Source/core/bridge triage:
- `source-facing`: the notation `Ω[f]` and universal derivation `d[f]` for a morphism of ringed
  sites `f : X ⟶ Y`;
- `core/canonical`: `SheafOfModules.RingedSite.relativeDifferentials` and
  `SheafOfModules.RingedSite.relativeDifferential`;
- `bridge/view`: `inverseImageStructureSheafMap f : f⁻¹𝒪_Y ⟶ 𝒪_X`.

This file therefore exposes only the source-facing notation on top of the generic-site owner,
matching the Chapter 17 ringed-space specialization pattern and deleting exact-interface local
wrappers. -/

/-- Definition 18.33.10: for a morphism `f : X ⟶ Y` of ringed sites, the sheaf of relative
differentials `Ω_{X/Y}` is the module of differentials of the inverse-image structure-sheaf map
`f^{-1}𝒪' ⟶ 𝒪`. We write this sheaf as `Ω[f]`. -/
abbrev relativeDifferentials (f : X ⟶ Y) : ringedSiteModuleCategory JC 𝒪 :=
  SheafOfModules.RingedSite.relativeDifferentials (f^♯)

/-- Helper for Definition 18.33.10: the universal `Y`-derivation attached to `Ω_{X/Y}` is the
canonical derivation of the inverse-image structure-sheaf map. We write it as `d[f]`. -/
abbrev relativeDifferential (f : X ⟶ Y) :
    Der[f^♯ ; relativeDifferentials f] :=
  SheafOfModules.RingedSite.relativeDifferential (f^♯)

scoped[RingedSite.Hom] notation3:max "Ω[" f "]" =>
  relativeDifferentials f

scoped[RingedSite.Hom] notation3:max "d[" f "]" =>
  relativeDifferential f

end

end RingedSite.Hom
