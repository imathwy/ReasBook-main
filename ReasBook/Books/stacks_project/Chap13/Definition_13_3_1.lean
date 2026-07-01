import Mathlib.CategoryTheory.Triangulated.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory.Pretriangulated

/- Domain-style sampling for Definition 13.3.1:
- primary domain: triangles in a category with shift, together with morphisms between such
  triangles;
- sampled core/canonical declarations:
  `Triangle`,
  `Triangle.mk`,
  `TriangleMorphism`,
  `Triangle.homMk`;
- primary owner abstraction: `Triangle`;
- companion morphism owner: `TriangleMorphism`;
- primitive data: the triangle object itself and, separately, the triple of component morphisms
  with the three commutative-square conditions for a morphism of triangles;
- derived API: `Triangle.mk` and `Triangle.homMk`, along with the induced category structure on
  triangles;
- source/core/bridge triage:
  `source-facing`: triangles `X ⟶ Y ⟶ Z ⟶ X[1]` and morphisms between them;
  `core/canonical`: `Triangle` and `TriangleMorphism`;
  `bridge/view`: the constructor API `Triangle.mk`/`Triangle.homMk` and later distinguished-triangle
    structure built on top of these owners.

Definition 13.3.1 is therefore a pure recall of the existing canonical owners, not a place for a
parallel local triangle or triangle-morphism wrapper. -/

/- Definition 13.3.1: the basic object `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` is the canonical owner `Triangle`. -/
recall Triangle

/- Companion check: the source-facing display `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` is built by the canonical
constructor `Triangle.mk`, so no parallel local triangle package is needed. -/
#check Triangle.mk

/- Companion recall: a morphism between such triangles is the canonical owner
`TriangleMorphism`. -/
recall TriangleMorphism

/- Companion check: the commutative-diagram data for a morphism of triangles is assembled by the
canonical constructor `Triangle.homMk`, so the file should not keep a duplicate local morphism
wrapper. -/
#check Triangle.homMk

end CategoryTheory.Pretriangulated
