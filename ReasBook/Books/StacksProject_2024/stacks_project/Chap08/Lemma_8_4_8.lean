import Mathlib
import StacksProject_2024.stacks_project.Chap04.Lemma_4_35_9
import StacksProject_2024.stacks_project.Chap08.Definition_8_4_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open Bicategory
open scoped Bicategory
open InducedCategory.Hom

/-
Domain-style sampling for Lemma 8.4.8:
- primary domain: morphisms of stacks over a site and the canonical over-base equivalence notion
  on their underlying based functors;
- sampled owner-level declarations:
  `StackOver`,
  `InducedCategory.Hom.toBasedFunctor`,
  `InducedCategory.Hom.IsEquivalenceOverBase`,
  `InducedCategory.Hom.LocallyEssentiallySurjectiveOnObjects`,
  `BasedFunctor.IsEquivalenceOverBase`,
  `FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects`;
- best owner abstraction: a stack morphism `F : X ⟶ Y` with `X Y : StackOver J`, using the
  Chapter 4 owner predicate `F.IsEquivalenceOverBase` on the underlying based functor;
- primitive data: the stack morphism `F`;
- derived API: the ambient fibred-category local-essential-surjectivity predicate transported to
  stack morphisms via `F.LocallyEssentiallySurjectiveOnObjects J`.

Source/core/bridge triage:
- `source-facing`: the equivalence-over-base criterion for morphisms of stacks over `(C, J)`;
- `core/canonical`: `StackOver`, `BasedFunctor.IsEquivalenceOverBase`, and
  `FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects`;
- `bridge/view`: `InducedCategory.Hom.toBasedFunctor`, `InducedCategory.Hom.IsEquivalenceOverBase`,
  and `InducedCategory.Hom.LocallyEssentiallySurjectiveOnObjects`. -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {X Y : StackOver J}

-- Proof sketch: if `F` is an equivalence over the base, then each target fiber object is already
-- in the essential image of the induced fiber functor, so the local condition is immediate. For
-- the converse, use full faithfulness to transport the local isomorphisms into descent data in
-- `X`, descend that datum using the stack condition on `X`, and then identify the image of the
-- descended object with the original target object, producing a quasi-inverse over `C`.
/-- Lemma 8.4.8: for a fully faithful `1`-morphism of stacks over `(C, J)`, being an equivalence
over the base is equivalent to being locally essentially surjective on objects of the fibers. -/
theorem isEquivalenceOverBase_iff_locallyEssentiallySurjectiveOnObjects
    (F : X ⟶ Y) (hF : Nonempty (toBasedFunctor F).FullyFaithful) :
    IsEquivalenceOverBase F ↔ LocallyEssentiallySurjectiveOnObjects J F := sorry

end CategoryTheory
