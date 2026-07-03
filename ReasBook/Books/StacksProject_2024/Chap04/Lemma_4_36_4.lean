import StacksProject_2024.Chap04.Lemma_4_36_4.Strictification

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Bicategory
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type (max u₁ u₂)} [Category.{max v₁ v₂} S]

/-- Lemma 4.36.4: every fibred category `p : S ⥤ C` admits a split strictification over
`C` and a based equivalence over `C` from `p` to that strictification. The strictification target
uses the larger object universe needed to store a base arrow in each strictified object. -/
lemma exists_split_fibred_category_over_base
    (p : S ⥤ C) [p.IsFibered] :
    ∃ (Y : FibredCategoryOver.{v₁, u₁, max u₁ (max u₂ v₁), max v₁ v₂} C)
      (F : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor Y.p),
      F.IsEquivalenceOverBase ∧ Functor.IsSplitFibredCategory Y.p := by
  exact exists_split_fibred_category_over_base_aux p

end CategoryTheory
