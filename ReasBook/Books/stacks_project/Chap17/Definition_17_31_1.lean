import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap17.«17_31_0_1»
import stacks_project.Chap17.Lemma_17_28_9
import stacks_project.Chap18.Definition_18_35_1

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
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})]
variable (𝒜 : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (𝒝 : Under 𝒜)

/- Domain-style sampling for Definition 17.31.1:
- primary domain: naive cotangent complexes of sheaves of `\mathcal A`-algebras on a space `X`;
- sampled owner declarations:
  `SheafOfModules.RingedSite.presentationNaiveCotangent`,
  `SheafOfModules.RingedSite.naiveCotangent`,
  `SheafOfModules.RingedSite.naiveCotangent_X_negOne`,
  `SheafOfModules.RingedSite.naiveCotangent_X_zero`;
- best owner abstraction: the generic site-level owner
  `SheafOfModules.RingedSite.naiveCotangent`, specialized to the opens site
  `Opens.grothendieckTopology X`;
- primitive data: the opens-site Grothendieck topology on `X`, the sheaf of rings `𝒜`, and the
  `𝒜`-algebra sheaf `𝒝 : Under 𝒜`;
- derived API: the opens-site specialization itself and its degree `-1/0` identification theorems,
  already owned upstream by Chapter 18.

Source/core/bridge triage:
- `source-facing`: the naive cotangent complex `NL_{\mathcal B/\mathcal A}` on a topological
  space;
- `core/canonical`: `SheafOfModules.RingedSite.naiveCotangent`;
- `bridge/view`: this file is only the opens-site specialization, so it should recall the
  canonical owner rather than maintain a second parallel definition. -/

/- Definition 17.31.1: for sheaves of rings `\mathcal A → \mathcal B` on a topological space
`X`, the naive cotangent complex `NL_{\mathcal B/\mathcal A}` is the canonical Chapter 18 owner
`SheafOfModules.RingedSite.naiveCotangent`, specialized to the opens site
`Opens.grothendieckTopology X`. -/
noncomputable abbrev naiveCotangent :
    CochainComplex
      (SheafOfModules (ringSheaf (Opens.grothendieckTopology X) 𝒝.right)) ℤ :=
  SheafOfModules.RingedSite.naiveCotangent
    (J := Opens.grothendieckTopology X) 𝒜 𝒝

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The degree `-1` term of `NL_{\mathcal B/\mathcal A}` is the conormal source
`\mathcal I/\mathcal I^2` of the canonical presentation `\mathcal A[\mathcal B] \to \mathcal B`.
-/
theorem naiveCotangent_X_negOne :
    (naiveCotangent 𝒜 𝒝).X (-1) =
      SheafOfModules.RingedSite.conormalSource (presentationMap 𝒜 𝒝) := by
  simpa using
    (SheafOfModules.RingedSite.naiveCotangent_X_negOne
      (J := Opens.grothendieckTopology X) 𝒜 𝒝)

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The degree `0` term of `NL_{\mathcal B/\mathcal A}` is the tensor term
`\mathcal B \otimes_{\mathcal A[\mathcal B]}
  \Omega_{\mathcal A[\mathcal B]/\mathcal A}` of the canonical presentation. -/
theorem naiveCotangent_X_zero :
    (naiveCotangent 𝒜 𝒝).X 0 =
      SheafOfModules.RingedSite.conormalTensorTerm
        (presentationBase 𝒜 𝒝) (presentationMap 𝒜 𝒝) := by
  simpa using
    (SheafOfModules.RingedSite.naiveCotangent_X_zero
      (J := Opens.grothendieckTopology X) 𝒜 𝒝)

end TopCat.Sheaf
