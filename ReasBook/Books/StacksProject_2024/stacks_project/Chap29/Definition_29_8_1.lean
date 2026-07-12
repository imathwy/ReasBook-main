import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical scheme-morphism owner
  `AlgebraicGeometry.IsDominant`;
- its source-faithful dense-image characterization is exactly
  `AlgebraicGeometry.isDominant_iff`.

This item is therefore `core/canonical`: Definition 29.8.1 only recalls the existing dominant
morphism owner, so the public surface should stay as a recall block rather than a duplicate alias.
-/

/- Definition 29.8.1: a morphism of schemes `f : X ⟶ S` is dominant if the image of the
underlying map on points is dense in `S`. This is the canonical mathlib predicate
`AlgebraicGeometry.IsDominant f`. -/
recall IsDominant

/- Companion recall: the textbook condition is exactly the dense-range characterization
`AlgebraicGeometry.isDominant_iff`. -/
recall isDominant_iff

end AlgebraicGeometry
