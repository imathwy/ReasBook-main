import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Tactic.Recall
import stacks_project.Chap12.Definition_12_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Limits

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/- Domain-style sampling for Definition 12.17.1:
- primary domain: monoidal categories whose underlying category is additive and whose tensor
  product is additive in each variable;
- sampled owner API:
  `Preadditive`,
  `HasFiniteProducts`,
  `HasFiniteBiproducts.of_hasFiniteProducts`,
  `MonoidalPreadditive`;
- source/core/bridge triage:
  `source-facing`: the additive underlying-category condition, expressed by the earlier chapter
    owners `Preadditive C` and `HasFiniteProducts C`;
  `core/canonical`: the tensor-additivity owner `MonoidalPreadditive C`;
  `bridge/view`: finite biproducts are derived from `HasFiniteProducts C` in a preadditive
    category, so they are not primitive data here.

Primitive data are only the ambient monoidal category, the preadditive enrichment, the finite
product structure encoding additivity from Definition 12.3.8, and the tensor-additivity owner
`MonoidalPreadditive C`, whose primitive whiskering-linearity data are recorded by
`MonoidalPreadditive.whiskerLeft_zero`, `MonoidalPreadditive.zero_whiskerRight`,
`MonoidalPreadditive.whiskerLeft_add`, and `MonoidalPreadditive.add_whiskerRight`. The additive
tensor-functor API is derived from that owner, so no extra local wrapper is needed.
-/
/- Companion recall: by Definition 12.3.8, the additive part of Definition 12.17.1 is carried by
the canonical owner pair `Preadditive C` and `HasFiniteProducts C`. -/
recall Preadditive
recall HasFiniteProducts

variable [Preadditive C] [HasFiniteProducts C]

/- Definition 12.17.1: an additive monoidal category is a monoidal category whose underlying
category is additive and whose tensor product is additive in each variable. Reusing the earlier
chapter owner for additivity, the new owner-level content is `MonoidalPreadditive C`. -/
recall MonoidalPreadditive

/- Companion recall: the owner stores linearity of tensoring in each variable via the primitive
zero and addition whiskering fields. -/
recall MonoidalPreadditive.whiskerLeft_zero
recall MonoidalPreadditive.zero_whiskerRight
recall MonoidalPreadditive.whiskerLeft_add
recall MonoidalPreadditive.add_whiskerRight

/- Companion recall: the tensoring functors are additive by the canonical derived API attached to
`MonoidalPreadditive C`. -/
recall tensorLeft_additive
recall tensorRight_additive

end CategoryTheory
