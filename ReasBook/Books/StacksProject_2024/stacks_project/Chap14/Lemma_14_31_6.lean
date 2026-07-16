import Mathlib
import StacksProject_2024.stacks_project.Chap14.Definition_14_31_1
import StacksProject_2024.stacks_project.Chap14.Lemma_14_31_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling for Lemma 14.31.6:
- primary domain: simplicial sets as fibrant objects in the Quillen model structure, viewed through
  the forgetful functor from simplicial groups;
- sampled owner declarations:
  `SSet.KanComplex`,
  `HomotopicalAlgebra.isFibrant_iff`,
  `SSet.KanComplex.hornFilling`,
  `SSet.modelCategoryQuillen.fibration_iff`;
- best owner abstraction: `SSet.KanComplex` as the canonical owner on the underlying simplicial
  set of a simplicial group;
- primitive-vs-derived split:
  primitive data: the simplicial group `X : SimplicialObject GrpCat`;
  derived API: the source-facing theorem `simplicialGroup_kanComplex X`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that the underlying simplicial set of a simplicial group is a
  Kan complex;
- `core/canonical`: the owner predicate `SSet.KanComplex`;
- `bridge/view`: the horn-filling and terminal-map characterizations of `KanComplex`.

This item is `source-facing`, but its exact owner-level interface is already available upstream as
the predicate `SSet.KanComplex`. There is no exact upstream theorem for simplicial groups, so the
correct refinement is to state the lemma directly with target `SSet.KanComplex`, rather than
pretending that a recall-style instance already exists. -/

instance instKanComplexUnderlyingSimplicialGroup (X : SimplicialObject GrpCat) :
    SSet.KanComplex (X ⋙ forget GrpCat) := by
  -- Reuse the adjacent local bridge theorem for simplicial groups.
  exact simplicialGroup_kanComplex_local X

/-- Lemma 14.31.6: the underlying simplicial set of a simplicial group is a Kan complex.
The canonical owner is `SSet.KanComplex`, so the public statement lands directly in that
predicate. -/
theorem simplicialGroup_kanComplex (X : SimplicialObject GrpCat) :
    SSet.KanComplex (X ⋙ forget GrpCat) :=
  instKanComplexUnderlyingSimplicialGroup X
