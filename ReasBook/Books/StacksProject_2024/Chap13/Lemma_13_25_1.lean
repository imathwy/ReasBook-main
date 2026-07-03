import Mathlib
import StacksProject_2024.Chap13.Lemma_13_10_6
import StacksProject_2024.Chap13.Lemma_13_20_3
import StacksProject_2024.Chap13.Proposition_13_23_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/-
Domain-style sampling:
- primary domain: bounded-below right derived functors computed via injective complexes and a lift
  of the homotopy resolution functor;
- sampled owner declarations:
  `HomotopyResolutionFunctor`,
  `Localization.Lifting`,
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)`,
  `mapBoundedBelowHomotopyToDerivedBelow`,
  `Functor.IsRightDerivedFunctor`;
- best owner abstraction: the canonical localization owner is
  `mapBoundedBelowHomotopyToDerivedBelow`, and the injective-complex inclusion is owned by
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)`; the localization lift itself is
  owned canonically by `Localization.Lifting`, and the passage through `K^+(\mathcal I)` is a
  bridge/view built from those owners rather than a separate root functor declaration;
- primitive data: the additive functor `F`, the homotopy resolution functor `j`, the lifted
  functor `j' : D^+(\mathcal A) ⥤ K^+(\mathcal I)`, and the explicit lift datum
  `hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j'`;
- existence data such as `[EnoughInjectives 𝒜]` belongs upstream, where one proves that
  a `HomotopyResolutionFunctor 𝒜` exists, not in this bridge lemma about a fixed choice;
- derived API: the comparison 2-cell and the induced `IsRightDerivedFunctor` structure on the
  composite through bounded-below injectives.

Source/core/bridge triage:
- `source-facing`: Lemma 13.25.1 itself;
- `core/canonical`: `mapBoundedBelowHomotopyToDerivedBelow`,
  `Localization.Lifting`,
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)`, and
  `Functor.IsRightDerivedFunctor`;
- `bridge/view`: the composite `j' ⋙
  ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) ⋙
  mapBoundedBelowHomotopyCategoryToDerivedBelow F`.
-/
local notation "DplusA" => boundedBelowDerivedCategory 𝒜
local notation "Q" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ DplusA)
local notation "KinjIncl" => ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
local notation "KinjToDplusB" =>
  KinjIncl ⋙ mapBoundedBelowHomotopyCategoryToDerivedBelow F

attribute [local instance] mapBoundedBelowHomotopyToDerivedBelow_isLocalization

/-- The comparison 2-cell from the cochain-level functor `K^+(\mathcal A) ⥤ D^+(\mathcal B)` to
the composite through a lifted injective-resolution functor `j'`, packaged by the canonical
localization-lift datum `hj'`. -/
noncomputable def resolutionLiftComparison
    (j : HomotopyResolutionFunctor 𝒜) (j' : DplusA ⥤ K⁺ᵢ(𝒜))
    (hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j') :
    mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
      Q ⋙ (j' ⋙ KinjToDplusB) :=
  Functor.whiskerRight j.ι (mapBoundedBelowHomotopyCategoryToDerivedBelow F) ≫
    (Functor.associator j.toFunctor KinjIncl
      (mapBoundedBelowHomotopyCategoryToDerivedBelow F)).hom ≫
    (Functor.isoWhiskerRight hj'.iso.symm KinjToDplusB).hom ≫
    (Functor.associator Q j' KinjToDplusB).hom

-- Proof sketch: by Lemma 13.20.1, every bounded-below complex of injective objects computes the
-- right derived functor of `K^+(\mathcal A) ⟶ D^+(\mathcal B)`. The functor `j'` sends a derived
-- object to such an injective representative, and the comparison 2-cell is induced from the
-- resolution quasi-isomorphism `ι`; hence the composite through `K^+(\mathcal I)` is itself a
-- right derived functor, and therefore is naturally isomorphic to `RF` by uniqueness.
/-- Lemma 13.25.1: if `j' : D^+(\mathcal A) ⥤ K^+(\mathcal I)` is the lift of a homotopy
resolution functor `j` through the localization functor `K^+(\mathcal A) ⥤ D^+(\mathcal A)`,
encoded by `hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j'`, then the composite
`j' ⋙ F` with the induced functor
`F : K^+(\mathcal I) ⥤ D^+(\mathcal B)` is a right derived functor of
`K^+(\mathcal A) ⥤ D^+(\mathcal B)`; equivalently, it is naturally isomorphic to the bounded-
below right derived functor `RF`. -/
theorem resolution_lift_comp_isRightDerivedFunctor
    (j : HomotopyResolutionFunctor 𝒜) (j' : DplusA ⥤ K⁺ᵢ(𝒜))
    (hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j') :
    (j' ⋙ KinjToDplusB).IsRightDerivedFunctor
      (resolutionLiftComparison F j j' hj')
      (Qis⁺(𝒜)) := sorry

end

end CategoryTheory
