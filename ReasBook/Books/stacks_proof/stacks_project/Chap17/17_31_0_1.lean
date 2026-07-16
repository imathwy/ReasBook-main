import Mathlib
import stacks_proof.stacks_project.Chap17.Definition_17_31_6
import stacks_proof.stacks_project.Chap18.«18_35_0_2»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits TopCat
open SheafOfModules.RingedSite

universe u

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [Limits.HasBinaryCoproducts (TopCat.Sheaf CommRingCat.{u} X)]
variable (𝒜 : TopCat.Sheaf CommRingCat.{u} X) (𝒝 : Under 𝒜)

local notation "JX" => Opens.grothendieckTopology X

private instance topCatSheaf_hasBinaryCoproducts :
    HasBinaryCoproducts (CategoryTheory.Sheaf JX CommRingCat.{u}) := by
  simpa [TopCat.Sheaf] using
    (inferInstance : HasBinaryCoproducts (TopCat.Sheaf CommRingCat.{u} X))

/- Domain-style sampling for 17.31.0.1:
- primary domain: the canonical polynomial presentation `\mathcal A[\mathcal B] \to \mathcal B`
  of a sheaf of `\mathcal A`-algebras on the opens site of `X`;
- sampled owner declarations:
  `SheafOfModules.RingedSite.presentationVariables`,
  `SheafOfModules.RingedSite.presentationFreeSheaf`,
  `SheafOfModules.RingedSite.presentationMap`,
  `SheafOfModules.RingedSite.presentationMap_on_brackets`,
  `Under.costarAdjForget`;
- best owner abstraction: the chapter already owns the presentation data at the generic site level
  in `SheafOfModules.RingedSite`, so this file should keep only the opens-site specialization and
  the source-facing bracket companion theorem;
- primitive data: the imported site-level presentation owners specialized to `JX`;
- derived API: only the bracket formula saying that the canonical presentation map sends the
  generator `[b]` to `b`.

Source/core/bridge triage:
- `source-facing`: `presentationMap_on_brackets`;
- `core/canonical`: the site-level owners
  `presentationVariables`, `presentationFreeSheaf`, `presentationBase`, `presentationMap`, and
  `presentationMap_on_brackets`;
- `bridge/view`: this file is only the opens-site specialization of those owners. -/

/- Equation 17.31.0.1: for the opens site `JX`, the bracket formula for the canonical
presentation morphism `\mathcal A[\mathcal B] \to \mathcal B` is already the generic-site owner
`SheafOfModules.RingedSite.presentationMap_on_brackets`, specialized to `J := JX`. -/
#check SheafOfModules.RingedSite.presentationMap_on_brackets 𝒜 𝒝

end TopCat.Sheaf
