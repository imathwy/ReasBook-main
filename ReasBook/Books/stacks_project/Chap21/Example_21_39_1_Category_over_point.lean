import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory

/-- Example 21.39.1 (Category over point): for a category `\mathcal C`, viewed with the chaotic
topology so that presheaves and sheaves agree, the `n`-th homology group of an abelian sheaf
`\mathcal F` on `\mathcal C` is the `n`-th left derived functor of taking colimits over
`\mathcal C^\mathrm{op}`. -/
abbrev categoryHomology {C : Type u} [Category.{v} C]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    AddCommGrpCat.{max u v} :=
  ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}).leftDerived n).obj ℱ

-- Proof sketch: unfold `categoryHomology`; it was defined to be the value of the `n`-th left
-- derived functor of the colimit functor on the abelian presheaf category `Cᵒᵖ ⥤ AddCommGrpCat`.
/-- The homology object of an abelian presheaf on `C` is, by definition, the value of the
`n`-th left derived functor of colimits over `Cᵒᵖ`. -/
theorem categoryHomology_eq_leftDerivedColimit {C : Type u} [Category.{v} C]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    categoryHomology ℱ n =
      ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}).leftDerived n).obj
        ℱ := sorry

end CategoryTheory
