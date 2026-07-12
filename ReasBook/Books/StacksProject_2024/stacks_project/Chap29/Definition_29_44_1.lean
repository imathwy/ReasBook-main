import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall / analogue check:
-- `lean_leansearch` recalled the exact canonical owners
-- `AlgebraicGeometry.IsIntegralHom`, `AlgebraicGeometry.isIntegralHom_iff`,
-- `AlgebraicGeometry.IsFinite`, and `AlgebraicGeometry.isFinite_iff`; nearby Chapter 29 files use
-- the same pure check/recall pattern when a Stacks definition exactly matches an existing mathlib
-- owner.

/- Definition 29.44.1 (1): a morphism of schemes `f : X ⟶ S` is integral if it is affine and, for
every affine open `U ⊆ S`, the induced ring map on sections is integral. This is exactly the
canonical morphism property `AlgebraicGeometry.IsIntegralHom`. -/
recall AlgebraicGeometry.IsIntegralHom

/- Companion recall for Definition 29.44.1 (1): the textbook affine-open characterization is the
theorem `AlgebraicGeometry.isIntegralHom_iff`. -/
recall AlgebraicGeometry.isIntegralHom_iff

/- Definition 29.44.1 (2): a morphism of schemes `f : X ⟶ S` is finite if it is affine and, for
every affine open `U ⊆ S`, the induced ring map on sections is finite. This is exactly the
canonical morphism property `AlgebraicGeometry.IsFinite`. -/
recall AlgebraicGeometry.IsFinite

/- Companion recall for Definition 29.44.1 (2): the textbook affine-open characterization is the
theorem `AlgebraicGeometry.isFinite_iff`. -/
recall AlgebraicGeometry.isFinite_iff
