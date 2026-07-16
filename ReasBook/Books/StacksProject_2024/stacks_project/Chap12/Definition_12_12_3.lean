import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap12.Definition_12_12_1

namespace CategoryTheory

/- Domain-style sampling:
- primary domain: universal cohomological `δ`-functors in an abelian-category setting.
- declarations inspected in the chapter owner API:
  `CohomologicalDeltaFunctor.Hom`,
  `CohomologicalDeltaFunctor.IsUniversal`,
  `CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso`.
- `source-facing`: the textbook predicate that a cohomological `δ`-functor is universal.
- `core/canonical`: `CohomologicalDeltaFunctor.IsUniversal`.
- `bridge/view`: the extension-and-uniqueness clause carried by the owner predicate.
- Primitive data vs derived API: the primitive owner data are the cohomological `δ`-functor and
  the owner universality predicate; the explicit extension-and-uniqueness statement for a fixed
  degree-zero morphism is derived API from that owner predicate.
-/

/- Definition 12.12.3: universality of a cohomological `δ`-functor is exactly the canonical
predicate `CohomologicalDeltaFunctor.IsUniversal`. -/
recall CohomologicalDeltaFunctor.IsUniversal

end CategoryTheory
