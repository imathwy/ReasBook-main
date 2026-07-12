import Mathlib.Tactic.Recall
import StacksProject_2024.Chap12.Definition_12_12_1

namespace CategoryTheory

/- Domain-style sampling:
- primary domain: morphisms of cohomological `δ`-functors between abelian categories.
- relevant upstream chapter declarations inspected in `Definition_12_12_1`:
  `CohomologicalDeltaFunctor.Hom`,
  `CohomologicalDeltaFunctor.Hom.app`,
  `CohomologicalDeltaFunctor.Hom.comm`,
  `CohomologicalDeltaFunctor.Hom.comp`.
- `source-facing`: the textbook notion of a morphism of cohomological `δ`-functors.
- `core/canonical`: `CohomologicalDeltaFunctor.Hom`.
- `bridge/view`: the degreewise component projection `CohomologicalDeltaFunctor.Hom.app` and the
  compatibility-square projection `CohomologicalDeltaFunctor.Hom.comm`.
- Primitive data vs derived API: the primitive owner data is exactly the degreewise natural
  transformation family together with compatibility with the connecting morphisms; identity,
  composition, and the category structure are derived API from that owner.
-/

/- Definition 12.12.2: a morphism of cohomological `δ`-functors is exactly the canonical owner
structure `CohomologicalDeltaFunctor.Hom`. -/
recall CohomologicalDeltaFunctor.Hom

end CategoryTheory
