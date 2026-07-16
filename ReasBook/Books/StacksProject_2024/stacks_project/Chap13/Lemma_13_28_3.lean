import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap13.Definition_13_28_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Domain-style sampling for Lemma 13.28.3:
- primary domain: triangulated Grothendieck groups and exact-functor functoriality;
- sampled owner declarations:
  `CategoryTheory.TriangulatedK0.lift`,
  `CategoryTheory.TriangulatedK0.lift_of`,
  `CategoryTheory.TriangulatedK0.map`,
  `CategoryTheory.TriangulatedK0.map_of`;
- source/core/bridge triage:
  `source-facing`: the exact-functoriality map on triangulated `K₀`;
  `core/canonical`: `CategoryTheory.TriangulatedK0.map`;
  `bridge/view`: `CategoryTheory.TriangulatedK0.map_of`, which evaluates the owner map on
    classes.

Primitive data are only the exact functor and the fact that it preserves distinguished triangles.
The quotient descent along `TriangulatedK0.lift` and its evaluation formula `lift_of` are derived
owner API from `Definition_13_28_1`, so this file should recall the existing owner instead of
reintroducing a parallel local map. -/

/- Lemma 13.28.3: the induced map on triangulated Grothendieck groups is the owner declaration
`CategoryTheory.TriangulatedK0.map`. -/
recall TriangulatedK0.map

/- Companion recall: the owner evaluation theorem on classes is
`CategoryTheory.TriangulatedK0.map_of`. -/
recall TriangulatedK0.map_of

end CategoryTheory
