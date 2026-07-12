import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism composition instances
-- `AlgebraicGeometry.IsProper.instCompScheme` and
-- `AlgebraicGeometry.universallyClosedTypeComp`, so this item is a direct recall of existing
-- mathlib API rather than a duplicate theorem wrapper.

/- Lemma 29.41.4 (1): the composition of proper morphisms is proper. This is exactly the
canonical scheme-side composition instance for `IsProper`. -/
recall AlgebraicGeometry.IsProper.instCompScheme

/- Lemma 29.41.4 (2): the composition of universally closed morphisms is universally closed. This
is exactly the canonical scheme-side composition instance for `UniversallyClosed`. -/
recall AlgebraicGeometry.universallyClosedTypeComp
