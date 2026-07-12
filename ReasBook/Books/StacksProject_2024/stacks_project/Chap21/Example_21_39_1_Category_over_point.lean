import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.LeftDerived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory

/-
Domain-style sampling for Example 21.39.1:
- primary domain: category homology of abelian presheaves on a category over a point, expressed
  canonically as a left derived colimit;
- sampled owner declarations:
  `colim`,
  `Functor.leftDerived`,
  `ProjectiveResolution.isoLeftDerivedObj`,
  `HomologicalComplex.homologyFunctor`;
- best owner abstraction: the source-facing notation `H_[n](C, ℱ)` should be only a thin bridge
  to the canonical mathlib owner `((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤
  AddCommGrpCat.{w}).leftDerived n).obj ℱ`, not a parallel chapter-local wrapper;
- primitive data: a category `C`, an abelian presheaf `ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}`, a degree
  `n : ℕ`, and the projective-resolution hypothesis on the presheaf category;
- derived API: the textbook surface notation `H_[n](C, ℱ)`, together with the degree-zero and
  projective-resolution computation recalls proved in
  `Example_21_39_2_Computing_homology`.

Source/core/bridge triage:
- `source-facing`: the homology object `H_n(\mathcal C, \mathcal F)` of a category over a point,
  written as `H_[n](C, ℱ)`;
- `core/canonical`: the left derived colimit owner `(colim).leftDerived`;
- `bridge/view`: the definitional identification
  `H_[n](C, ℱ) = ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).leftDerived n).obj ℱ`.
  -/

section

variable {C : Type u} [Category.{v} C]
variable [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
variable [HasProjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{w})]

namespace CategoryHomology

/-- Example 21.39.1: the category homology object `H_n(C, ℱ)` of an abelian presheaf `ℱ` on `C`,
defined as the `n`-th left derived object of colimit. -/
abbrev categoryHomology (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    AddCommGrpCat.{w} :=
  ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).leftDerived n).obj ℱ

/- Textbook surface notation for the source-facing category homology object `H_n(C, ℱ)`. The
displayed category argument is checked by coercing `ℱ` through the presheaf category on `C`, and
the notation expands to `categoryHomology ℱ n`. -/
scoped notation3
  "H_[" n:max "](" C ", " ℱ ")" =>
  categoryHomology ℱ n

end CategoryHomology

open scoped CategoryHomology

variable (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ)

/-- Companion bridge: the source-facing owner `categoryHomology ℱ n`, and hence the notation
`H_[n](C, ℱ)`, is definitionally the canonical `n`-th left derived colimit object. -/
theorem categoryHomology_eq_leftDerivedObj :
    H_[n](C, ℱ) = (colim.leftDerived n).obj ℱ :=
  rfl

end

end CategoryTheory
