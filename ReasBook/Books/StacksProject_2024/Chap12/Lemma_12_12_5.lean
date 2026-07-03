import Mathlib.Tactic.Recall
import stacks_project.Chap12.Definition_12_12_1

namespace CategoryTheory

/- Domain-style sampling:
- primary domain: universal cohomological `δ`-functors in an abelian-category setting.
- declarations inspected in the chapter owner API:
  `CohomologicalDeltaFunctor.Hom`,
  `CohomologicalDeltaFunctor.IsUniversal`,
  the extension-and-uniqueness clause carried by `CohomologicalDeltaFunctor.IsUniversal`,
  `CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso`.
- `source-facing`: the uniqueness-up-to-unique-isomorphism statement for universal cohomological
  `δ`-functors with prescribed degree-zero identification.
- `core/canonical`: `CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso`.
- `bridge/view`: none needed here, since the textbook lemma already coincides with the owner
  theorem.
- Primitive data vs derived API: the primitive data are the owner object
  `CohomologicalDeltaFunctor`, its morphisms `CohomologicalDeltaFunctor.Hom`, the universality
  predicate `CohomologicalDeltaFunctor.IsUniversal`, and the prescribed degree-zero isomorphisms;
  uniqueness up to unique isomorphism is derived API from that owner layer.
-/

/- Lemma 12.12.5: the uniqueness-up-to-unique-isomorphism statement for universal cohomological
`δ`-functors is the owner theorem
`CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso`. -/
recall CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso

end CategoryTheory
