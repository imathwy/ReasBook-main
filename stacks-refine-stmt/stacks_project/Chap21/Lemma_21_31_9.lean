import Mathlib
import stacks_project.Chap21.Definition_21_31_2
import stacks_project.Chap21.Situation_21_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

/-- Proper maps in `LC` viewed as a morphism property. -/
abbrev lcProperMapProperty : MorphismProperty LCCat.{u} :=
  fun _ _ f ↦ IsProperMap f.hom

/-- Membership in `lcProperMapProperty` is exactly topological properness. -/
theorem mem_lcProperMapProperty_iff {X Y : LCCat.{u}} (f : X ⟶ Y) :
    lcProperMapProperty f ↔ IsProperMap f.hom :=
  Iff.rfl

section

variable (τzar : GrothendieckTopology LCCat.{u})
variable (πFunctor : ∀ X : LCCat.{u}, Opens X.obj ⥤ Over X)
variable [∀ X : LCCat.{u},
  Functor.IsContinuous (πFunctor X) (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [∀ X : LCCat.{u},
  ((πFunctor X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint]

/-- The inverse-image functor `π_X^{-1}` on abelian sheaves from the small Zariski site of `X` to
the big Zariski site `LC_{Zar}/X`. -/
abbrev lcZarPiInverseAb (X : LCCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj ⥤
      Sheaf (τzar.over X) AddCommGrpCat.{u + 1} :=
  (πFunctor X).sheafPullback AddCommGrpCat.{u + 1} (Opens.grothendieckTopology X.obj) (τzar.over X)

/-- For `X ∈ LC`, the comparison subcategory `A'_X ⊂ Ab(LC_{Zar}/X)` consists of the sheaves in
the essential image of `π_X^{-1}`. -/
abbrev lcZarPiInverseEssImage (X : LCCat.{u}) :
    ObjectProperty (Sheaf (τzar.over X) AddCommGrpCat.{u + 1}) :=
  (lcZarPiInverseAb τzar πFunctor X).essImage

/-- Membership in `A'_X` means that the sheaf is isomorphic to one of the form `π_X^{-1}\mathcal
F`. -/
theorem mem_lcZarPiInverseEssImage_iff
    {X : LCCat.{u}} (ℱ : Sheaf (τzar.over X) AddCommGrpCat.{u + 1}) :
    lcZarPiInverseEssImage τzar πFunctor X ℱ ↔
      (lcZarPiInverseAb τzar πFunctor X).essImage ℱ :=
  Iff.rfl

end

section

variable (τqc τzar : GrothendieckTopology LCCat.{u})
variable (πFunctor : ∀ X : LCCat.{u}, Opens X.obj ⥤ Over X)
variable [∀ X : LCCat.{u},
  Functor.IsContinuous (πFunctor X) (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [∀ X : LCCat.{u},
  ((πFunctor X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint]
variable [∀ X : LCCat.{u},
  Functor.IsContinuous (𝟭 (Over X)) (τzar.over X) (τqc.over X)]
variable [∀ X : LCCat.{u},
  ((𝟭 (Over X)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (τzar.over X) (τqc.over X)).IsRightAdjoint]
variable [∀ X : LCCat.{u}, HasInjectiveResolutions (Sheaf (τzar.over X) AddCommGrpCat.{u + 1})]
variable [∀ {X Y : LCCat.{u}} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (τzar.over X) (τzar.over Y))]

-- Proof sketch: for each `X`, Lemma `21.31.7` identifies `A'_X` with the essential image of the
-- exact fully faithful functor `π_X^{-1}`, giving the weak Serre conditions. Proper maps in `LC`
-- are stable under base change, Lemma `21.31.6` shows objects of `A'_X` are already sheaves for
-- the qc topology, Lemma `21.31.7` gives compatibility of inverse image and higher direct images
-- with `π_X^{-1}` for proper maps, and Lemma `21.31.4` supplies the refinement clause for qc
-- coverings.
/-- Lemma 21.31.9: for the comparison morphism `LC_qc ⟶ LC_Zar`, let `P` be the proper maps of
topological spaces and let `A'_X ⊂ Ab(LC_Zar / X)` be the full subcategory consisting of sheaves
of the form `π_X^{-1}\mathcal F`. Then the hypotheses `(1)` through `(5)` of Situation `21.30.1`
hold, formalized as a cohomology comparison situation. -/
theorem lc_qc_lc_zar_cohomology_comparison_situation :
    cohomology_comparison_situation τqc τzar
      lcProperMapProperty (lcZarPiInverseEssImage τzar πFunctor) := sorry

end

end CategoryTheory.GrothendieckTopology
