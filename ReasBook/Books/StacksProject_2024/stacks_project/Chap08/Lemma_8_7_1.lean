import Mathlib
import StacksProject_2024.stacks_project.Chap04.«4_34_2_1»
import StacksProject_2024.stacks_project.Chap04.Lemma_4_34_1
import StacksProject_2024.stacks_project.Chap04.Lemma_4_42_1
import StacksProject_2024.stacks_project.Chap08.Definition_8_6_1
import StacksProject_2024.stacks_project.Chap08.Definition_8_6_5
import StacksProject_2024.stacks_project.Chap08.Definition_8_5_5
import StacksProject_2024.stacks_project.Chap08.Lemma_8_5_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open Bicategory.InducedBicategory

variable {C : Type u} [Category.{v} C]

section

variable {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 8.7.1:
- primary domain: relative and absolute inertia of morphisms of stacks over a site.
- inspected owner-level declarations:
  `FibredCategoryOver.relativeInertiaOver`,
  `FibredCategoryOver.absoluteInertiaOver`,
  `StackOver`,
  `StackInGroupoidsOver`,
  `StackInSetoidsOver`.
- best owner abstraction: Chapter 4 already owns the inertia objects as fibred categories over the
  base, so this file should state only the Chapter 8 closure results saying that those owner
  objects are again stacks, stacks in groupoids, and stacks in setoids.
- primitive data: a morphism of fibred categories over `C` whose source and target satisfy the
  relevant stack, stack-in-groupoids, or stack-in-setoids owner predicates.
- derived API: the stack-closure theorems and the rebundled `StackOver` views
  `relativeInertiaStack` and `absoluteInertiaStack`.

Source/core/bridge triage:
- `source-facing`: the closure statements in Lemma 8.7.1.
- `core/canonical`: `FibredCategoryOver.relativeInertiaOver` and
  `FibredCategoryOver.absoluteInertiaOver`.
- `bridge/view`: the bundled `StackOver` abbreviations below. -/

-- Proof sketch: identify the relative inertia with the explicit iterated `2`-fibre product from
-- Lemma `4.34.1`, apply Lemma `8.4.6` to that explicit model, and specialize the same argument to
-- the absolute inertia.
/-- Lemma 8.7.1 (1): the relative inertia of a morphism of stacks over `(C, J)` and the absolute
inertia of its source are again stacks over `(C, J)`. -/
theorem relative_and_absolute_inertia_are_stacks
    {X Y : FibredCategoryOver C} [IsStackOnSite J X.p] [IsStackOnSite J Y.p] (F : X ⟶ Y) :
    IsStackOnSite J
        (FibredCategoryOver.relativeInertiaOver F).p ∧
      IsStackOnSite J
        (FibredCategoryOver.absoluteInertiaOver X).p := sorry

-- Proof sketch: use the same relative-inertia/iterated-`2`-fibre-product identification from
-- Lemma `4.34.1`, then invoke Lemma `8.5.6` for the explicit `2`-fibre product and specialize to
-- the absolute inertia of the source stack.
/-- Lemma 8.7.1 (2): if the source and target are stacks in groupoids over `(C, J)`, then the
relative inertia and the absolute inertia of the source are also stacks in groupoids over
`(C, J)`. -/
theorem relative_and_absolute_inertia_are_stacks_in_groupoids
    {X Y : FibredCategoryOver C}
    [IsStackInGroupoids J X.p] [IsStackInGroupoids J Y.p] (F : X ⟶ Y) :
    IsStackInGroupoids J
        (FibredCategoryOver.relativeInertiaOver F).p ∧
      IsStackInGroupoids J
        (FibredCategoryOver.absoluteInertiaOver X).p := sorry

/-- The relative inertia of a morphism of stacks over `(C, J)`, viewed again as a stack over
`(C, J)`. -/
abbrev relativeInertiaStack
    {X Y : FibredCategoryOver C} [IsStackOnSite J X.p] [IsStackOnSite J Y.p] (F : X ⟶ Y) :
    StackOver J :=
  ⟨
    FibredCategoryOver.relativeInertiaOver F,
    (relative_and_absolute_inertia_are_stacks F).1
  ⟩

/-- The absolute inertia of a stack over `(C, J)` is again a stack over `(C, J)`. -/
instance absoluteInertiaOver_isStackOnSite
    (X : FibredCategoryOver C) [IsStackOnSite J X.p] :
    IsStackOnSite J (FibredCategoryOver.absoluteInertiaOver X).p := sorry

/-- The absolute inertia of a stack over `(C, J)`, viewed again as a stack over `(C, J)`. -/
abbrev absoluteInertiaStack (X : FibredCategoryOver C) [IsStackOnSite J X.p] :
    StackOver J :=
  ⟨
    FibredCategoryOver.absoluteInertiaOver X,
    inferInstance
  ⟩

-- Proof sketch: combine Lemma `4.34.1` with Lemma `8.6.6` for the explicit iterated
-- `2`-fibre-product model of relative inertia to obtain the setoid-fiber condition, while the
-- stack condition itself comes from the stack case above.
/-- Lemma 8.7.1 (3): if the source and target are stacks in setoids over `(C, J)`, then the
relative inertia of the morphism and the absolute inertia of the source are again stacks in
setoids over `(C, J)`. -/
theorem relative_and_absolute_inertia_are_stacks_in_setoids
    {X Y : FibredCategoryOver C}
    [IsStackInSetoids J X.p] [IsStackInSetoids J Y.p] (F : X ⟶ Y) :
    IsStackInSetoids J
        (FibredCategoryOver.relativeInertiaOver F).p ∧
      IsStackInSetoids J
        (FibredCategoryOver.absoluteInertiaOver X).p := sorry

/-- The absolute inertia of a stack in setoids is again a stack in setoids. -/
instance absoluteInertiaOver_isStackInSetoids
    (X : FibredCategoryOver C) [IsStackInSetoids J X.p] :
    IsStackInSetoids J (FibredCategoryOver.absoluteInertiaOver X).p := sorry

end

end CategoryTheory
