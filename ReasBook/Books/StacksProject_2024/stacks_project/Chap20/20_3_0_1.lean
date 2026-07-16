import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DerivedCategory.TStructure
open scoped CategoryTheory

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

/- Domain sampling:
- primary domain: bounded-below derived categories and bounded-below right derived functors
  computed from a homotopy-resolution lift;
- sampled canonical/project declarations:
  - `t.plus`
  - `D⁺(X)`
  - `derivedCategory_t_plus_iff`
  - `HomotopyResolutionFunctor`
  - `Localization.Lifting`
  - `Functor.totalRightDerived`
  - `Functor.rightDerivedUnique`
- best owner abstraction: the bounded-below owner is the canonical full subcategory `D⁺(X)` cut
  out by `t.plus`, while the source-facing factorization statement for bounded-below right derived
  functors is the specialization of the canonical owner `Functor.rightDerivedUnique` to the
  Chapter 13 resolution-lift data;
- primitive vs. derived:
  - primitive data: the canonical owner `t.plus`, an additive functor `F : 𝒜 ⥤ ℬ`, a homotopy
    resolution functor `j`, a lift `j' : D⁺(𝒜) ⥤ K⁺ᵢ(𝒜)`, and the localization lift datum `hj'`;
  - derived API: the low-degree vanishing criterion `derivedCategory_t_plus_iff` and the
    comparison isomorphism from the canonical bounded-below right derived functor to the composite
    through bounded-below injectives.

Source/core/bridge triage:
- `source-facing`: eventual low-degree vanishing and the textbook factorization `RF = F ∘ j'`;
- `core/canonical`: `t.plus`, `D⁺(X)`, `Localization.Lifting`, and
  `Functor.totalRightDerived` / `Functor.rightDerivedUnique`;
- `bridge/view`: `derivedCategory_t_plus_iff` and the specialization of
  `Functor.rightDerivedUnique` to the Chapter 13 resolution-lift comparison.
-/

section

variable {X : Type u₁} [Category.{v₁} X] [Abelian X] [HasDerivedCategory.{w} X]

/- Owner recall: the bounded-below property on `D(X)` is the canonical `t`-structure owner
`t.plus`. -/
#check (t.plus : ObjectProperty (DerivedCategory X))

/- Owner recall: `D⁺(X)` is the canonical full subcategory cut out by that owner property. -/
#check (D⁺(X) : Type _)

/- 20.3.0.1 (1): Chapter 13 already exposes the eventual low-degree vanishing specification of
the bounded-below owner, in the chapter notation `D⁺(X)` and `H^i`. -/
recall derivedCategory_t_plus_iff
    (K : DerivedCategory X) :
    (t.plus : ObjectProperty (DerivedCategory X)) K ↔
      ∃ n : ℤ, ∀ i < n, Limits.IsZero ((H^i).obj K)

end

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]
  [Functor.HasRightDerivedFunctor
    (mapBoundedBelowHomotopyCategoryToDerivedBelow F)
    (Qis⁺(𝒜))]

local notation "DplusA" => D⁺(𝒜)
local notation "Q" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ DplusA)
local notation "KinjIncl" => ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
local notation "KinjToDplusB" =>
  KinjIncl ⋙ mapBoundedBelowHomotopyCategoryToDerivedBelow F
local notation "RT" =>
  Functor.totalRightDerived (mapBoundedBelowHomotopyCategoryToDerivedBelow F) Q (Qis⁺(𝒜))
local notation "αRT" =>
  Functor.totalRightDerivedUnit (mapBoundedBelowHomotopyCategoryToDerivedBelow F) Q (Qis⁺(𝒜))

/- Canonical owner recall: once the Chapter 13 resolution-lift comparison is fixed and known to
exhibit the composite through bounded-below injectives as a right derived functor, the source
formula `RF = F ∘ j'` is exactly the specialized uniqueness isomorphism
`Functor.rightDerivedUnique`. -/
recall Functor.rightDerivedUnique

/- Companion recall: the defining factorization of that specialized comparison is the canonical
identity `Functor.rightDerived_fac`. -/
recall Functor.rightDerived_fac

/- 20.3.0.1 (2): for a homotopy resolution functor `j`, a lift
`j' : D⁺(𝒜) ⥤ K⁺ᵢ(𝒜)`, and lift datum `hj'`, the textbook factorization
`RF = F ∘ j'` is the canonical comparison
`RT ≅ j' ⋙ KinjToDplusB` attached to the explicit map
`resolutionLiftComparison F j j' hj'`. Lemma `13.25.1` supplies the displayed right-derived
witness for this specialization. -/
variable (j : HomotopyResolutionFunctor 𝒜) (j' : D⁺(𝒜) ⥤ K⁺ᵢ(𝒜))
  (hj' :
    Localization.Lifting
      (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜))
      (Qis⁺(𝒜))
      j.toFunctor
      j')

local notation "RTinj" => j' ⋙ KinjToDplusB
local notation "βRT" => resolutionLiftComparison F j j' hj'

#check
  ((RT).rightDerivedUnique RTinj αRT βRT (Qis⁺(𝒜)) : RT ≅ RTinj)

/- Companion bridge: the comparison isomorphism above is characterized by the canonical
factorization relation attached to `rightDerivedDesc`. -/
#check
  ((RT).rightDerived_fac αRT (Qis⁺(𝒜)) RTinj βRT :
    αRT ≫ Functor.whiskerLeft Q ((RT).rightDerivedDesc αRT (Qis⁺(𝒜)) RTinj βRT) = βRT)

end

end CategoryTheory
