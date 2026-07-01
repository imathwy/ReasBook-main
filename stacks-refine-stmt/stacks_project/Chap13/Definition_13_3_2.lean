import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Domain-style sampling:
- primary domain: triangulated categories, organized around distinguished triangles and the
  octahedron axiom;
- relevant upstream owner declarations in this domain:
  `Pretriangulated`,
  `Pretriangulated.distinguishedTriangles`,
  `IsTriangulated`,
  `IsTriangulated.mk'`;
- source/core/bridge triage:
  `source-facing`: the Stacks definition of a triangulated category via distinguished triangles
    satisfying TR1--TR4;
  `core/canonical`: `Pretriangulated` for the distinguished-triangle data with TR1--TR3, and
    `IsTriangulated` for adding TR4;
  `bridge/view`: `distTriang` as the induced distinguished-triangle owner and
    `IsTriangulated.mk'` as the canonical constructor used downstream to verify TR4.

Primitive data is the pretriangulated structure; the octahedron axiom is derived as the extra
owner proposition `IsTriangulated`. Definition 13.3.2 is therefore a pure recall of the existing
canonical owners, not a place for any local wrapper or duplicate predicate.
-/

/- Definition 13.3.2: in mathlib, the choice of distinguished triangles together with
axioms TR1, TR2, and TR3 is packaged by `Pretriangulated`, and a
triangulated category is obtained by adding the octahedron axiom TR4, formalized by the
canonical class `IsTriangulated`. -/
recall IsTriangulated

/- Companion recall: the pre-triangulated part of the definition, namely the distinguished
triangles satisfying TR1, TR2, and TR3, is formalized by the canonical class
`Pretriangulated`. -/
recall Pretriangulated

end CategoryTheory
