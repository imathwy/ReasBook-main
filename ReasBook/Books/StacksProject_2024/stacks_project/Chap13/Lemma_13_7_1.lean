import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Domain-style sampling for Lemma 13.7.1:
- primary domain: exactness of adjoint functors between pretriangulated categories;
- sampled owner declarations:
  `Adjunction.rightAdjointCommShift`,
  `Adjunction.isTriangulated_rightAdjoint`;
- best owner abstraction: the source-facing owner is the exactness theorem for the right adjoint
  `Adjunction.isTriangulated_rightAdjoint`; the bundled predicate `adj.IsTriangulated` is a
  derived package on the whole adjunction, not the main conclusion of this lemma.

Primitive-vs-derived split:
- primitive data: an adjunction `adj : F ⊣ G` and exactness of the left adjoint, encoded by
  `[F.CommShift ℤ] [F.IsTriangulated]`;
- derived API: the canonical right-adjoint shift data `G.CommShift ℤ`, the induced adjunction
  compatibility `adj.CommShift ℤ`, and the bundled exactness package `adj.IsTriangulated`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that a right adjoint of an exact functor is exact;
- `core/canonical`: `Adjunction.isTriangulated_rightAdjoint`, together with the canonical derived
  shift data `Adjunction.rightAdjointCommShift` and `Adjunction.commShift_of_leftAdjoint`;
- `bridge/view`: the chapter reading of exactness through the owner pair
  `Functor.CommShift ℤ` and `Functor.IsTriangulated`, where the adjunction API supplies the
  derived right-adjoint shift instances needed before applying the owner theorem.

This item is therefore a direct recall of the canonical right-adjoint exactness theorem, not a
new local wrapper around the bundled adjunction package.
-/

/- Lemma 13.7.1: if `F ⊣ G` and `F` is exact, then `G` is exact. In the canonical API, after
instantiating `G.CommShift ℤ` and `adj.CommShift ℤ` via
`Adjunction.rightAdjointCommShift` and `Adjunction.commShift_of_leftAdjoint`, this is exactly the
canonical theorem `Adjunction.isTriangulated_rightAdjoint`. -/
recall Adjunction.isTriangulated_rightAdjoint

end CategoryTheory
