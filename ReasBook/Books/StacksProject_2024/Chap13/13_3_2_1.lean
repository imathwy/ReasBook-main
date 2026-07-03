import Mathlib.CategoryTheory.Triangulated.Rotate
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Pretriangulated

/- Domain-style sampling for 13.3.2.1:
- primary domain: triangle rotation in a pretriangulated category, used to read off the
  bi-infinite display attached to a triangle from its successive rotations;
- sampled core/canonical declarations:
  `Triangle.rotate`,
  `Triangle.invRotate`,
  `CategoryTheory.Pretriangulated.rotate`,
  `CategoryTheory.Pretriangulated.invRotate`;
- best owner abstraction: the object-level canonical owners `Triangle.rotate` and
  `Triangle.invRotate`;
- primitive data: a single triangle `T : Triangle C`;
- derived API: the functorial rotation operators `rotate` and `invRotate` on `Triangle C`;
- source/core/bridge triage:
  `source-facing`: the displayed bi-infinite sequence attached to a triangle;
  `core/canonical`: `Triangle.rotate` and `Triangle.invRotate`;
  `bridge/view`: the right-hand and left-hand segments identified with those canonical rotations.

No parallel local sequence declaration is needed: the source display is already owned canonically
by triangle rotation. -/

/- 13.3.2.1: the displayed bi-infinite sequence attached to a triangle
`X ⟶ Y ⟶ Z ⟶ X⟦1⟧` is given canonically by triangle rotation; the right-hand segment
`Y ⟶ Z ⟶ X⟦1⟧ ⟶ Y⟦1⟧` is exactly `Triangle.rotate`, whose third morphism is `-f⟦1⟧'`. -/
recall Triangle.rotate

/- Companion recall: the left-hand segment `Z⟦-1⟧ ⟶ X ⟶ Y ⟶ Z` of the same display is the
canonical inverse rotation `Triangle.invRotate`, whose first morphism is `-h⟦(-1 : ℤ)⟧'`
up to the built-in shift-equivalence identifications. -/
recall Triangle.invRotate
