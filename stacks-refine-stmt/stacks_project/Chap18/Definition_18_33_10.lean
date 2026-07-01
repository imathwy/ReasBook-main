import Mathlib
import stacks_project.Chap18.Definition_18_31_3
import stacks_project.Chap18.Lemma_18_33_2

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
  `AlgebraicGeometry.RingedSpace.differentials`;
- best owner abstraction: the bundled morphism `f : X ⟶ Y`, with source-facing surface
  `Ω[f] = Ω_{X/Y}` and `d[f]`;
- primitive data: only the bundled morphism `f : X ⟶ Y`;
- derived API: the inverse-image structure-sheaf map `inverseImageStructureSheafMap f`, the sheaf
  of differentials `Ω[f]`, the relative derivation type `Derivation f F`, and the universal
  derivation `d[f]`.

Source/core/bridge triage:
- `source-facing`: the owner `Ω[f]` and universal derivation `d[f]` for a morphism of ringed
  sites `f : X ⟶ Y`;
- `core/canonical`: `SheafOfModules.RingedSite.relativeDifferentials` and
  `SheafOfModules.RingedSite.relativeDifferential`;
- `bridge/view`: `inverseImageStructureSheafMap f : f⁻¹𝒪_Y ⟶ 𝒪_X`.

This file therefore upgrades the public API from the bridge datum `f⁻¹𝒪_Y ⟶ 𝒪_X` to the bundled
owner `f : X ⟶ Y`, matching Chapter 17's source-facing differentials surface. -/

/-- Definition 18.33.10: the sheaf of relative differentials of a bundled morphism of ringed
sites `f : X ⟶ Y`. -/
abbrev differentials (f : X ⟶ Y) : SheafOfModules (ringSheaf JC 𝒪) :=
  Ω(inverseImageStructureSheafMap f)

scoped[RingedSite.Hom] notation3:max "Ω[" f "]" => RingedSite.Hom.differentials f

/-- The type of relative derivations from `\mathcal O_X` to an `\mathcal O_X`-module along
`f : X ⟶ Y`. -/
abbrev Derivation (f : X ⟶ Y) (F : SheafOfModules (ringSheaf JC 𝒪)) : Type _ :=
  Der[inverseImageStructureSheafMap f ; F]

/-- The sheaf of differentials of a bundled morphism is the generic owner specialized along its
inverse-image structure-sheaf map. -/
theorem differentials_def (f : X ⟶ Y) :
    Ω[f] = Ω(inverseImageStructureSheafMap f) :=
  rfl

/-- The universal derivation `d_{X/Y} : \mathcal O_X \to Ω_{X/Y}` attached to a bundled morphism
of ringed sites. -/
abbrev differential (f : X ⟶ Y) : Derivation f Ω[f] :=
  relativeDifferential (inverseImageStructureSheafMap f)

scoped[RingedSite.Hom] notation3:max "d[" f "]" => RingedSite.Hom.differential f

end

end RingedSite.Hom
