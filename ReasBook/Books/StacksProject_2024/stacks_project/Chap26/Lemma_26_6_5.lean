import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical affine-scheme global-sections functor
-- `AffineScheme.Γ : AffineSchemeᵒᵖ ⥤ CommRingCat` and its equivalence instances.  The source
-- equivalence with the opposite category of rings is the right-opposite functor
-- `AffineScheme.Γ.rightOp : AffineScheme ⥤ CommRingCatᵒᵖ`.

/- Lemma 26.6.5: the category of affine schemes is equivalent to the opposite of the category of
commutative rings, via the functor sending an affine scheme to the global sections of its structure
sheaf. -/
recall AlgebraicGeometry.AffineScheme.Γ
recall AlgebraicGeometry.AffineScheme.instIsEquivalenceOppositeCommRingCatRightOpΓ

end AlgebraicGeometry
