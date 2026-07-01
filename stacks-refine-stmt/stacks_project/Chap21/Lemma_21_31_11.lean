import Mathlib
import stacks_project.Chap21.Definition_21_31_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.GrothendieckTopology

section

variable (QcSheaf : LCCat.{u} → Type (u + 1))
variable [∀ X : LCCat.{u}, Category.{u} (QcSheaf X)]
variable [∀ X : LCCat.{u}, Abelian (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj)]
variable [∀ X : LCCat.{u}, Abelian (QcSheaf X)]
variable [∀ X : LCCat.{u}, HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj)]
variable [∀ X : LCCat.{u}, HasDerivedCategory (QcSheaf X)]

variable (aInverseDerived :
  ∀ X : LCCat.{u},
    DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj) ⥤
      DerivedCategory (QcSheaf X))
variable (aPushforwardDerived :
  ∀ X : LCCat.{u},
    DerivedCategory (QcSheaf X) ⥤
      DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj))

/-- The bounded-below condition on the derived category `D(X)` of abelian sheaves on the small
site of `X`. -/
private def smallAbDerivedBoundedBelow (X : LCCat.{u}) :
    ObjectProperty (DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj)) :=
  fun K ↦
    ∃ n : ℤ, ∀ i : ℤ, i < n →
      Limits.IsZero
        ((DerivedCategory.homologyFunctor
          (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj) i).obj K)

-- Proof sketch: represent `K` by a bounded-below complex of abelian sheaves. For a single sheaf
-- `ℱ`, Lemma `21.31.6` identifies `a_{X,*} a_X^{-1} ℱ` with `ℱ`, while Lemma `21.31.10`
-- together with the relative Leray spectral sequence and Lemma `21.31.7` kills the higher
-- derived direct images. Leray's acyclicity lemma then upgrades the sheaf-level statement to the
-- bounded-below derived category, proving that the adjunction unit is an isomorphism.
/-- Lemma 21.31.11: for `X ∈ LC_{qc}` and `K ∈ D^+(X)`, the canonical map
`K ⟶ R a_{X,*} a_X^{-1} K` is an isomorphism. Here this map is formalized as the adjunction unit
for the chosen inverse-image functor `a_X^{-1}` on derived categories and the derived direct image
functor `R a_{X,*}` attached to the localization morphism
`a_X : Sh(LC_{qc}/X) ⟶ Sh(X)`. -/
theorem lcQc_localization_derived_unit_isIso
    (X : LCCat.{u})
    (adjA : aInverseDerived X ⊣ aPushforwardDerived X)
    (K : DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj))
    (hK : smallAbDerivedBoundedBelow X K) :
    IsIso (adjA.unit.app K) := sorry

end

end CategoryTheory.GrothendieckTopology
