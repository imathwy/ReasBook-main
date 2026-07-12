import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap04.Definition_4_35_1
import StacksProject_2024.Chap08.Lemma_8_10_4.ChosenPullbackEquivalence
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

namespace FibredCategoryOver

variable {C : Type u} [Category.{v} C]

/-- Lemma 8.10.4: if `X` is a category fibred in groupoids over the site `(C, J)` and `x : X.S`
lies over `U = X.p.obj x`, then the induced slice functor `X/x ⥤ C/U` is an equivalence of
categories, which is the categorical core of the textbook equivalence of sites. -/
@[stacks 0CN0]
theorem overPost_isEquivalence_of_isFibredInGroupoids
    (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] (x : X.S) :
    (Over.post X.p : Over x ⥤ Over (X.p.obj x)).IsEquivalence := by
  -- The heavy chosen-pullback comparison lives in the helper file so this public item stays thin.
  simpa using overPost_isEquivalence_of_isFibredInGroupoids_aux X x

end FibredCategoryOver

end CategoryTheory
