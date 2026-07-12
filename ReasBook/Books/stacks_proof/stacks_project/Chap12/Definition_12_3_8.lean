import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Tactic.Recall

universe v u

namespace CategoryTheory

open Limits

variable (A : Type u) [Category.{v} A]

/- Domain-style sampling for Definition 12.3.8:
- primary domain: additive structure on a preadditive category via finite limits/biproducts;
- sampled owner declarations:
  `HasFiniteProducts`,
  `HasFiniteBiproducts.of_hasFiniteProducts`,
  `hasZeroObject_of_hasFiniteBiproducts`;
- best owner abstraction: `HasFiniteProducts A`;
- primitive data: the preadditive enrichment and the finite-product structure;
- derived API: finite biproducts, direct sums, and the zero object. -/
/- Source/core/bridge triage for Definition 12.3.8:
- source-facing: in the source, an additive category is a preadditive category with finite
  products
- core/canonical owner: `HasFiniteProducts A`
- bridge/view: `HasFiniteBiproducts.of_hasFiniteProducts` supplies direct sums, and the zero object
  is then inferred canonically -/
section

variable [Preadditive A]

/- Definition 12.3.8: once `A` is preadditive, the source condition that `A` be additive is
exactly the canonical limit structure `HasFiniteProducts A`. -/
recall HasFiniteProducts

section

variable [HasFiniteProducts A]

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/- Companion bridge: the source-level direct-sum clause is the upstream owner theorem
`HasFiniteBiproducts.of_hasFiniteProducts`; after installing that canonical instance, the
zero-object owner is the standard derived instance `hasZeroObject_of_hasFiniteBiproducts A`. -/
recall HasFiniteBiproducts.of_hasFiniteProducts
#check (hasZeroObject_of_hasFiniteBiproducts A : HasZeroObject A)

end

end

end CategoryTheory
