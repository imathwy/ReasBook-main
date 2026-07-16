import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap18.Lemma_18_35_2

open CategoryTheory
open CategoryTheory.Limits
open TopCat
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts (X.Sheaf CommRingCat.{u})]

local notation "JX" => Opens.grothendieckTopology X

private instance topCatSheaf_hasBinaryCoproducts :
    HasBinaryCoproducts (CategoryTheory.Sheaf JX CommRingCat.{u}) := by
  simpa [TopCat.Sheaf] using
    (inferInstance : HasBinaryCoproducts (TopCat.Sheaf CommRingCat.{u} X))

variable (𝒜 : X.Sheaf CommRingCat.{u}) (𝒝 : Under 𝒜)

local notation "ModB" => SheafOfModules (ringSheaf JX 𝒝.right)
local notation "DModB" => DerivedCategory ModB

local instance : HasDerivedCategory ModB :=
  HasDerivedCategory.standard ModB

/- Domain-style sampling for Lemma 17.31.2:
- primary domain: presentation-independence of naive cotangent complexes for sheaves of
  `\mathcal A`-algebras on the opens site of a topological space;
- sampled owner declarations:
  `SheafOfModules.RingedSite.presentationVariables`,
  `SheafOfModules.RingedSite.presentationNaiveCotangentOf`,
  `SheafOfModules.RingedSite.naiveCotangent`,
  `SheafOfModules.RingedSite.presentationNaiveCotangent_iso`;
- best owner abstraction: the Chapter 18 site-level comparison theorem
  `presentationNaiveCotangent_iso`, specialized to `JX = Opens.grothendieckTopology X`;
- primitive data: a sheaf of sets `E`, a locally surjective map
  `α : E ⟶ presentationVariables 𝒝`, and the resulting presentation
  `presentationMapOf 𝒜 𝒝 E α : \mathcal A[E] ⟶ \mathcal B`;
- derived API: the derived-category objects
  `Q.obj (presentationNaiveCotangentOf E α)` and
  `Q.obj (SheafOfModules.RingedSite.naiveCotangent 𝒜 𝒝)`.

Source/core/bridge triage:
- `source-facing`: the statement that the naive cotangent complex attached to a chosen
  presentation of `\mathcal B` is isomorphic in `D(\mathcal B)` to the canonical
  `NL_{\mathcal B/\mathcal A}`;
- `core/canonical`: the site-level owners `presentationNaiveCotangentOf`, `naiveCotangent`, and
  `presentationNaiveCotangent_iso`;
- `bridge/view`: this file is only the opens-site specialization, so it should recall the Chapter
  18 owner theorem directly rather than introduce a second named theorem with the same interface. -/

/- Lemma 17.31.2: for a locally surjective presentation
`α : E ⟶ presentationVariables 𝒝` of the `\mathcal A`-algebra sheaf `\mathcal B`, the
presentationwise naive cotangent complex and the canonical naive cotangent complex determine
canonically isomorphic objects of `D(\mathcal B)`. This is exactly the Chapter 18 owner theorem
`presentationNaiveCotangent_iso`, specialized to the opens site of `X`. -/
recall presentationNaiveCotangent_iso

end TopCat.Sheaf
