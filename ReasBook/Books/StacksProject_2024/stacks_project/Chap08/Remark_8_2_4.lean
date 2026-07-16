import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_35_6
import StacksProject_2024.stacks_project.Chap08.Lemma_8_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite

universe u v

namespace CategoryTheory

open BasedFunctor
open FibredCategoryMor

variable {C : Type u} [Category.{v} C]
variable {X Y : FibredInGroupoidsOver C}

namespace FibredInGroupoidsMor

/- Domain-style sampling for Remark 8.2.4:
- primary domain: morphisms of categories fibred in groupoids over a fixed base and the induced
  canonical Hom-presheaf morphisms on fibers;
- sampled owner-level declarations:
  `FibredInGroupoidsMor.IsEquivalenceOverBase`,
  `BasedFunctor.isEquivalence_of_isEquivalenceOverBase`,
  `Functor.FullyFaithful.ofFullyFaithful`,
  `FibredCategoryMor.fibredMorphismPresheafMap_isIso_of_fullyFaithful`;
- best owner abstraction: the owner morphism `F : FibredInGroupoidsMor X Y`, with the
  equivalence-over-base predicate as primitive data; the Hom-presheaf isomorphism is derived API
  obtained by upgrading `F.toBasedFunctor` to an equivalence, then to the canonical fully
  faithful owner witness, and finally routing through the ambient
  `FibredCategoryMor.fibredMorphismPresheafMap_isIso_of_fullyFaithful` theorem;
- primitive data: only `F` together with `hF : F.IsEquivalenceOverBase`;
- derived API: `F.toBasedFunctor.IsEquivalence`, the resulting canonical fully faithful witness,
  and finally the `IsIso` statement for the comparison morphism `F.fibredMorphismPresheafMap x y`.

Source/core/bridge triage:
- `source-facing`: the remark-level conclusion that an equivalence over the base preserves the
  presheaves `Mor(x, y)`;
- `core/canonical`: `FibredInGroupoidsMor.IsEquivalenceOverBase`,
  `BasedFunctor.isEquivalence_of_isEquivalenceOverBase`,
  `Functor.FullyFaithful.ofFullyFaithful`, and
  `FibredCategoryMor.fibredMorphismPresheafMap_isIso_of_fullyFaithful`;
- `bridge/view`: the theorem below, which derives the source-facing conclusion from those owner
  abstractions without introducing a parallel presheaf API. -/

/-- Remark 8.2.4, in canonical form: for an equivalence over the base category `C`, the canonical
Hom-presheaf morphism from Lemma `8.2.3` is an isomorphism. Combined with
Lemma `4.37.3`, this is the source-faithful observation that one may replace a category fibred in
groupoids by an equivalent split model without changing the presheaves `Mor(x, y)`. -/
-- Proof sketch: upgrade the equivalence-over-base hypothesis to a fully faithful underlying based
-- functor, then apply the Chapter 8 isomorphism criterion for the canonical Hom-presheaf map.
theorem fibredMorphismPresheafMap_isIso_of_isEquivalenceOverBase
    (F : FibredInGroupoidsMor X Y) (hF : F.IsEquivalenceOverBase)
    {U : C} (x y : X.p.Fiber U) :
    IsIso (fibredMorphismPresheafMap
      (F : X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) x y) := sorry

end FibredInGroupoidsMor

end CategoryTheory
