import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Domain-style sampling:
- primary domain: triangulated categories, specifically the octahedron axiom and its reduction to
  a convenient isomorphic composable pair;
- sampled owner declarations in this domain:
  `Pretriangulated`,
  `IsTriangulated`,
  `Octahedron.ofIso`,
  `IsTriangulated.mk'`;
- best owner abstraction: the constructor `IsTriangulated.mk'`, which directly packages the source
  reduction principle for TR4 into the canonical owner `IsTriangulated`;
- primitive data vs derived API: the primitive data is exactly the reduced octahedron witness for
  an isomorphic replacement of a composable pair. The ambient triangulated-category structure is
  then derived by the owner constructor, so no local wrapper or duplicate reformulation is needed.

Source/core/bridge triage:
- `source-facing`: the Stacks reduction principle for proving TR4 after replacing a composable pair
  by an isomorphic one carrying distinguished triangles;
- `core/canonical`: `IsTriangulated`;
- `bridge/view`: `Octahedron.ofIso`, internalized by the constructor `IsTriangulated.mk'`.
-/

/- Lemma 13.4.15: to prove TR4 for a pre-triangulated category, it suffices to verify the
octahedron axiom after replacing any composable pair of morphisms by an isomorphic pair
`X' ⟶ Y' ⟶ Z'` for which the triangles on `f'`, `g'`, and `g' ≫ f'` are distinguished. This
reduction principle is exactly the canonical constructor `CategoryTheory.IsTriangulated.mk'`. -/
recall IsTriangulated.mk'

end CategoryTheory
