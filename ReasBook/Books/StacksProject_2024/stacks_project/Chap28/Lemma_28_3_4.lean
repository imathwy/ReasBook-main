import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` surfaced the exact canonical theorem
-- `AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced`. This matches the source item,
-- while the preceding local items `Lemma 28.3.2` and `Lemma 28.3.3` package the reduced and
-- irreducible sides separately in chapter-local form.

/- Lemma 28.3.4: a scheme `X` is integral if and only if it is reduced and irreducible. This is
the canonical theorem `AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced`, with
irreducibility expressed by `IrreducibleSpace X`. -/
recall AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced
