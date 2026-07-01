import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory
namespace Pretriangulated

/- Domain-style sampling:
- primary domain: morphisms of distinguished triangles in a pretriangulated category and the
  triangle-level two-out-of-three isomorphism principle;
- sampled upstream owner declarations:
  `Triangle`,
  `TriangleMorphism`,
  `isIso₂_of_isIso₁₃`,
  `isIso₃_of_isIso₁₂`,
  `isIso₁_of_isIso₂₃`;
- best owner abstraction:
  `source-facing`: the three Stacks clauses asserting that in a morphism of distinguished
    triangles, any two isomorphic components force the third to be an isomorphism;
  `core/canonical`: the owner lemmas `isIso₂_of_isIso₁₃`, `isIso₃_of_isIso₁₂`, and
    `isIso₁_of_isIso₂₃` in `CategoryTheory.Pretriangulated`;
  `bridge/view`: none, because the source statements already coincide with the canonical
    owner-level theorems.

Primitive data are only the triangle morphism and the distinguishedness assumptions on its source
and target triangles. The isomorphism conclusion for the remaining component is derived API from
the canonical owner lemmas, so this file should remain a pure recall file with no parallel local
wrapper declarations.
-/

/- Lemma 13.4.3 (1): for a morphism of distinguished triangles in a pre-triangulated category, if
the first and third components are isomorphisms, then the second component is an isomorphism.
This is exactly the canonical theorem `isIso₂_of_isIso₁₃`. -/
recall isIso₂_of_isIso₁₃

/- Lemma 13.4.3 (2): for a morphism of distinguished triangles in a pre-triangulated category, if
the first and second components are isomorphisms, then the third component is an isomorphism.
This is exactly the canonical theorem `isIso₃_of_isIso₁₂`. -/
recall isIso₃_of_isIso₁₂

/- Lemma 13.4.3 (3): for a morphism of distinguished triangles in a pre-triangulated category, if
the second and third components are isomorphisms, then the first component is an isomorphism.
This is exactly the canonical theorem `isIso₁_of_isIso₂₃`. -/
recall isIso₁_of_isIso₂₃

end Pretriangulated
end CategoryTheory
