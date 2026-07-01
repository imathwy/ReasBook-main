import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable (A : Type u) [Category.{v} A]

/- Domain-style sampling for Definition 12.3.1:
- primary domain: preadditive categories and additive functors;
- sampled owner API:
  `Preadditive`,
  `Preadditive.preadditiveHasZeroMorphisms`,
  `Functor.Additive`,
  `Functor.mapAddHom`;
- best owner abstraction: `Preadditive A` for the additive enrichment on `A`, and
  `Functor.Additive` for additivity of functors between preadditive categories.

Primitive data live in the owner classes `Preadditive` and `Functor.Additive`. Zero morphisms are
derived from `Preadditive`, and the additive-hom API for a functor is derived from
`Functor.Additive`, so neither should be rebuilt as parallel local data.
-/
/- Source/core/bridge triage for Definition 12.3.1:
- source-facing: the additive enrichment on hom-sets, and the additivity property for functors
  between such categories
- core/canonical owners: `Preadditive A` and `Functor.Additive`
- bridge/view: `Limits.HasZeroMorphisms A` is derived API from `Preadditive A`, so it should not
  appear as parallel primitive data -/
/- Definition 12.3.1 (1): a preadditive category is a category whose hom-sets are abelian groups
and whose composition law is bilinear in both variables; this is the canonical mathlib class
`CategoryTheory.Preadditive`. -/
recall Preadditive

section

variable [Preadditive A]

/- Companion recall: in a preadditive category, zero morphisms are derived API via the canonical
instance `Preadditive.preadditiveHasZeroMorphisms`, so the owner-level statement remains
`Preadditive A`. -/
#synth Limits.HasZeroMorphisms A

end

/- Definition 12.3.1 (2): for preadditive categories, an additive functor is a functor whose map
on every hom-group is an additive homomorphism; this is the canonical mathlib class
`CategoryTheory.Functor.Additive`. -/
recall Functor.Additive

end CategoryTheory
