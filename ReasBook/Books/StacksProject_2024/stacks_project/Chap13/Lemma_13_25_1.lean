import Mathlib
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap13.Definition_13_23_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Localization
open CategoryTheory.ObjectProperty
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

private abbrev Q : K⁺(𝒜) ⥤ D⁺(𝒜) :=
  mapBoundedBelowHomotopyToDerivedBelow

private abbrev KinjIncl : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜) :=
  ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)

private abbrev KinjToDplusB : K⁺ᵢ(𝒜) ⥤ D⁺(ℬ) :=
  KinjIncl ⋙ mapBoundedBelowHomotopyCategoryToDerivedBelow F

/- Lemma 13.25.1 is a bridge statement: for a chosen lift `j'` of a homotopy resolution functor,
the comparison with the canonical bounded-below right derived functor is the natural
transformation induced by `j.ι` and the localization-lift isomorphism. -/
/-- The comparison 2-cell from the cochain-level functor `K^+(\mathcal A) ⥤ D^+(\mathcal B)` to
the composite through a lifted injective-resolution functor `j'`, packaged by the canonical
localization-lift datum `hj'`. -/
noncomputable def resolutionLiftComparison
    (j : HomotopyResolutionFunctor 𝒜) (j' : D⁺(𝒜) ⥤ K⁺ᵢ(𝒜))
    (hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j') :
    mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
      Q ⋙ (j' ⋙ KinjToDplusB F) :=
  Functor.whiskerRight j.ι (mapBoundedBelowHomotopyCategoryToDerivedBelow F) ≫
    (Functor.associator j.toFunctor (KinjIncl (𝒜 := 𝒜))
      (mapBoundedBelowHomotopyCategoryToDerivedBelow F)).hom ≫
    (Functor.isoWhiskerRight hj'.iso.symm (KinjToDplusB (F := F))).hom ≫
    (Functor.associator Q j' (KinjToDplusB (F := F))).hom

/-- Lemma 13.25.1: if `j' : D^+(\mathcal A) ⥤ K^+(\mathcal I)` is the lift of a homotopy
resolution functor `j` through the localization functor `K^+(\mathcal A) ⥤ D^+(\mathcal A)`,
encoded by `hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j'`, then the composite
`j' ⋙ F` with the induced functor
`F : K^+(\mathcal I) ⥤ D^+(\mathcal B)` is a right derived functor of
`K^+(\mathcal A) ⥤ D^+(\mathcal B)`; equivalently, it is naturally isomorphic to the bounded-
below right derived functor `RF`. -/
theorem resolution_lift_comp_isRightDerivedFunctor
    (j : HomotopyResolutionFunctor 𝒜) (j' : D⁺(𝒜) ⥤ K⁺ᵢ(𝒜))
    (hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j') :
    (j' ⋙ KinjToDplusB F).IsRightDerivedFunctor
      (resolutionLiftComparison F j j' hj')
      (Qis⁺(𝒜)) := by
  sorry

/-- The comparison attached to a lifted homotopy resolution computes the canonical bounded-below
right derived functor. -/
instance resolutionLiftComparison_isRightDerivedFunctor
    (j : HomotopyResolutionFunctor 𝒜) (j' : D⁺(𝒜) ⥤ K⁺ᵢ(𝒜))
    (hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j') :
    (j' ⋙ KinjToDplusB F).IsRightDerivedFunctor
      (resolutionLiftComparison F j j' hj')
      (Qis⁺(𝒜)) :=
  resolution_lift_comp_isRightDerivedFunctor F j j' hj'

end

end CategoryTheory
