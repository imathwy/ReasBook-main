import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` found the exact scheme-morphism owner
-- `AlgebraicGeometry.IsAffineHom` and its source-faithful characterization
-- `AlgebraicGeometry.isAffineHom_iff`.

/- Definition 29.11.1: a morphism of schemes `f : X ⟶ S` is affine if the inverse image of every
affine open of `S` is an affine open of `X`. This is the canonical mathlib predicate
`AlgebraicGeometry.IsAffineHom f`. -/
recall AlgebraicGeometry.IsAffineHom

/- Companion recall: the textbook condition is exactly the characterization
`AlgebraicGeometry.isAffineHom_iff`. -/
recall AlgebraicGeometry.isAffineHom_iff
