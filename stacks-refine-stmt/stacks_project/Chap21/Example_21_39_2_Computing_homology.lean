import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable [HasProjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]

/-- The category homology functor `H_n(\mathcal C, -)` on abelian presheaves is the `n`-th left
derived functor of the colimit functor on `Cᵒᵖ`. -/
abbrev categoryHomology (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    AddCommGrpCat.{max u v} :=
  ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}).leftDerived n).obj ℱ

-- Proof sketch: this is immediate from the definition of `categoryHomology` as the `n`-th left
-- derived colimit functor on abelian presheaves.
/-- Unfolding `categoryHomology` identifies it with the `n`-th left derived colimit. -/
theorem categoryHomology_eq_leftDerivedColimit (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    categoryHomology ℱ n =
      ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}).leftDerived n).obj
        ℱ := sorry

/-- The degree-zero category homology of an abelian presheaf is its ordinary colimit. -/
abbrev categoryHomology_zero_iso_colimit (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    categoryHomology ℱ 0 ≅
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}).obj ℱ :=
  ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}).leftDerivedZeroIsoSelf).app
    ℱ

/-- Example 21.39.2 (Computing homology): if `P` is a projective resolution of an abelian
presheaf `ℱ` on `C`, then applying colimits termwise to `P.complex` gives a chain complex whose
`n`-th homology computes `H_n(\mathcal C, \mathcal F)`. This is the categorical form of the
explicit complex `K_\bullet(\mathcal F)` described in the text. -/
abbrev categoryHomology_iso_homology_of_projectiveResolution
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (P : ProjectiveResolution ℱ) (n : ℕ) :
    categoryHomology ℱ n ≅
      (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).obj
        (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) :=
  P.isoLeftDerivedObj
    (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}) n

-- Proof sketch: unfold `categoryHomology_iso_homology_of_projectiveResolution`; the displayed
-- isomorphism is exactly the standard projective-resolution computation isomorphism
-- `P.isoLeftDerivedObj` for the colimit functor.
/-- Unfolding the comparison isomorphism for category homology computed from `P` recovers the
standard projective-resolution isomorphism for the colimit functor. -/
theorem categoryHomology_iso_homology_of_projectiveResolution_def
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (P : ProjectiveResolution ℱ) (n : ℕ) :
    categoryHomology_iso_homology_of_projectiveResolution ℱ P n =
      P.isoLeftDerivedObj
        (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}) n := sorry

end

end CategoryTheory
