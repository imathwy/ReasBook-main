import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` surfaced the canonical morphism property
-- `AlgebraicGeometry.Surjective`, together with the bridge theorems
-- `AlgebraicGeometry.surjective_iff` and
-- `AlgebraicGeometry.surjective_eq_topologically`.

/- Definition 29.9.1: this is a pure canonical recall. A morphism of schemes is surjective exactly
when it is surjective on the underlying topological spaces, and mathlib already packages this
source-facing owner as `AlgebraicGeometry.Surjective`. -/
#check AlgebraicGeometry.Surjective

/- Companion recall: the source formulation is exactly the characterization
`AlgebraicGeometry.surjective_iff`. -/
#check AlgebraicGeometry.surjective_iff

/- Companion recall: the topological-space reformulation is
`AlgebraicGeometry.surjective_eq_topologically`. -/
#check AlgebraicGeometry.surjective_eq_topologically
