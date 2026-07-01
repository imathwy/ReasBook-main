import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Domain-style sampling for 14.34.1.1:
- primary domain: adjunctions of functors and their triangle identities;
- sampled owner API:
  `CategoryTheory.Adjunction`,
  `Adjunction.left_triangle`,
  `Adjunction.right_triangle`,
  `Adjunction.left_triangle_components`;
- source/core/bridge triage:
  `source-facing`: the two composites built from the adjunction unit and counit;
  `core/canonical`: `CategoryTheory.Adjunction F G`;
  `bridge/view`: the componentwise triangle identities
  `Adjunction.left_triangle_components` and `Adjunction.right_triangle_components`.

Primitive data are the unit and counit carried by `Adjunction`; the triangle identities are
derived theorems of that owner abstraction. Therefore this item should be stated by direct recall
of the canonical theorems, not by introducing local composite definitions or wrapper lemmas.
-/

/- 14.34.1.1 (1): for an adjunction `U ⊣ V`, the composite
`V ⟶ V ⋙ U ⋙ V ⟶ V` built from the unit `η` and counit `d` is the identity natural
transformation. This is exactly the canonical theorem `CategoryTheory.Adjunction.right_triangle`. -/
recall Adjunction.right_triangle

/- 14.34.1.1 (2): for an adjunction `U ⊣ V`, the composite
`U ⟶ U ⋙ V ⋙ U ⟶ U` built from the unit `η` and counit `d` is the identity natural
transformation. This is exactly the canonical theorem `CategoryTheory.Adjunction.left_triangle`. -/
recall Adjunction.left_triangle

end CategoryTheory
