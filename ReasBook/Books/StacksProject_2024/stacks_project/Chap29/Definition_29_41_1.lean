import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` surfaced the exact scheme-morphism owner
-- `AlgebraicGeometry.IsProper` together with the source-faithful characterization
-- `AlgebraicGeometry.isProper_iff`.

/- Definition 29.41.1: for a morphism of schemes `f : X ⟶ S`, the textbook definition of
properness as “separated, finite type, and universally closed” is exactly the canonical mathlib
owner `AlgebraicGeometry.IsProper f`. -/
recall AlgebraicGeometry.IsProper

/- Companion recall: the source clauses are unpacked by the characterization
`AlgebraicGeometry.isProper_iff`. -/
recall AlgebraicGeometry.isProper_iff
