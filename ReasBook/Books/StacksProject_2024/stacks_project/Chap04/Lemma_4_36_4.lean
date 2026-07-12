import Mathlib
import StacksProject_2024.Chap04.Definition_4_33_9
import StacksProject_2024.Chap04.Definition_4_36_2

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open FibredCategoryOver
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/- Domain-style sampling for Lemma 4.36.4:
- primary domain: fibred categories over a fixed base and equivalences in `Cat/C` to split
  fibred categories.
- sampled owner declarations:
  `FibredCategoryOver`,
  `Bicategory.Equivalence`,
  `Functor.IsSplitFibredCategory`,
  `FibredCategoryMor.exists_equivalence`,
  `FibredCategoryOver.hom_isEquivalenceOverBase`.
- best owner abstraction: a split model should be exposed as an object `Y : FibredCategoryOver C`;
  the additional source-facing datum is then only the split predicate
  `Y.p.IsSplitFibredCategory`, while the comparison to `p` should use the ambient owner
  equivalence `FibredCategoryOver.ofFunctor p ≌ Y`; the explicit morphism
  `e.hom : FibredCategoryOver.ofFunctor p ⟶ Y` and its predicate `e.hom.IsEquivalenceOverBase`
  are derived bridge data.
- primitive data: the fibred functor `p : S ⥤ C` and a split category over `C`.
- derived API: the forward owner morphism `e.hom` together with
  `FibredCategoryOver.hom_isEquivalenceOverBase e`; any explicit contravariant `Cat`-valued
  co-Grothendieck model is secondary bridge/view data recovered from the split target via
  `Functor.IsSplitFibredCategory.existsCoGrothendieckModel`.

Source/core/bridge triage:
- `source-facing`: the existence of a split fibred category over `C` equivalent over the base to
  `p`.
- `core/canonical`: `FibredCategoryOver C`, `Bicategory.Equivalence`, and
  `Functor.IsSplitFibredCategory`.
- `bridge/view`: the explicit contravariant `Cat`-valued functor model recovered from the split
  target via `Functor.IsSplitFibredCategory.existsCoGrothendieckModel`, and the forward owner
  morphism `e.hom` together with `FibredCategoryOver.hom_isEquivalenceOverBase e`. -/

-- Proof sketch: choose pullbacks for `p`, strictify them as in Lemma 4.36.3 to obtain a split
-- fibred category over `C`, and compare `p` with that split model by an equivalence in
-- `FibredCategoryOver C`. Any explicit `Cat`-valued co-Grothendieck presentation is recovered
-- afterward from the split target via `Functor.IsSplitFibredCategory.existsCoGrothendieckModel`.

/-- Lemma 4.36.4: every fibred category `p : S ⥤ C` is equivalent over `C` to a split fibred
category over `C`. By Definition 4.36.2, the split target is source-faithfully one that is
isomorphic over `C` to a contravariant `Cat`-valued co-Grothendieck model. -/
lemma exists_split_fibred_category_over_base
    (p : S ⥤ C) [p.IsFibered] :
    ∃ (Y : FibredCategoryOver C) (e : ofFunctor p ≌ Y),
      Y.p.IsSplitFibredCategory := by
  sorry

end CategoryTheory
