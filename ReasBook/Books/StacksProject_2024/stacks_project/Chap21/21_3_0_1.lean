import StacksProject_2024.stacks_project.Chap13.Lemma_13_25_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒪 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒪] [Category.{v₂} ℬ]
  [Abelian 𝒪] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒪] [HasDerivedCategory.{w} ℬ]
  (F : 𝒪 ⥤ ℬ) [F.Additive]
  [Functor.HasRightDerivedFunctor
    (mapBoundedBelowHomotopyCategoryToDerivedBelow F)
    (Qis⁺(𝒪))]

/- Domain sampling:
- primary domain: bounded-below right derived functors computed via injective resolutions;
- sampled canonical/project declarations:
  - `Functor.totalRightDerived`
  - `Functor.rightDerivedUnique`
  - `resolution_lift_comp_isRightDerivedFunctor`
  - `mapBoundedBelowHomotopyCategoryToDerivedBelow`
- best owner abstraction: the canonical bounded-below right derived functor
  `Functor.totalRightDerived (mapBoundedBelowHomotopyCategoryToDerivedBelow F) Q (Qis⁺(𝒪))`,
  with the comparison to a chosen lift owned by `Functor.rightDerivedUnique`;
- primitive data: the additive functor `F`, a homotopy resolution functor `j`, a lift
  `j' : D⁺(𝒪) ⥤ K⁺ᵢ(𝒪)`, and the localization lift datum
  `Localization.Lifting Q (Qis⁺(𝒪)) j.toFunctor j'`;
- derived API: the source-facing identification of the bounded-below right derived functor with
  the composite through `j'`, using the bridge
  `resolution_lift_comp_isRightDerivedFunctor`.

Source/core/bridge triage:
- `source-facing`: the formula `RF ≅ F ∘ j'` after choosing the lift `j'`;
- `core/canonical`: `Functor.totalRightDerived` and `Functor.rightDerivedUnique`;
- `bridge/view`: `resolution_lift_comp_isRightDerivedFunctor`, which exhibits the composite
  through injective representatives as a right derived functor of the same source functor.

This item is therefore not just the raw composite `j' ⋙ F`; the mathematical content is the
canonical comparison isomorphism from the bounded-below right derived functor to that composite. -/

local notation "Q" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒪) ⥤ D⁺(𝒪))
local notation "DplusO" => D⁺(𝒪)
local notation "KinjIncl" => ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒪)
local notation "KinjToDplusB" => KinjIncl ⋙ mapBoundedBelowHomotopyCategoryToDerivedBelow F
local notation "RF" =>
  Functor.totalRightDerived (mapBoundedBelowHomotopyCategoryToDerivedBelow F) Q (Qis⁺(𝒪))
local notation "αRF" =>
  Functor.totalRightDerivedUnit (mapBoundedBelowHomotopyCategoryToDerivedBelow F) Q (Qis⁺(𝒪))

/- Canonical owner recall: the factorization of the bounded-below right derived functor through a
chosen lift `j'` is the corresponding specialization of `Functor.rightDerivedUnique`. -/
#check Functor.rightDerivedUnique

/- 21.3.0.1: after choosing a homotopy resolution functor `j` and a lift
`j' : D⁺(𝒪) ⥤ K⁺ᵢ(𝒪)`, the bounded-below right derived functor of `F` is canonically identified
with the composite through `j'`; the bridge making this precise is
`resolution_lift_comp_isRightDerivedFunctor`, and the source-facing comparison isomorphism itself
is the corresponding specialization of `Functor.rightDerivedUnique`. -/
#check resolution_lift_comp_isRightDerivedFunctor

/-- 21.3.0.1: after choosing a homotopy resolution functor `j` and a lift
`j' : D⁺(𝒪) ⥤ K⁺ᵢ(𝒪)`, the bounded-below right derived functor of `F` is canonically isomorphic
to the composite through `j'`. This source-facing proposition is the specialization of
`Functor.rightDerivedUnique` determined by `resolutionLiftComparison`; the file intentionally
records the canonical comparison via `IsIsomorphic` rather than by choosing a public `Iso`
witness. -/
@[stacks 05U5]
theorem boundedBelowRightDerivedResolutionLift_isomorphic
    (j : HomotopyResolutionFunctor 𝒪) (j' : DplusO ⥤ K⁺ᵢ(𝒪))
    (hj' : Localization.Lifting Q (Qis⁺(𝒪)) j.toFunctor j') :
    IsIsomorphic RF (j' ⋙ KinjToDplusB) := by
  exact
    ⟨(RF).rightDerivedUnique
      (j' ⋙ KinjToDplusB) αRF (resolutionLiftComparison F j j' hj') (Qis⁺(𝒪))⟩

end

end CategoryTheory
