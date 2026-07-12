import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found the exact canonical mathlib instance
-- `AlgebraicGeometry.instLocallyQuasiFiniteOfIsImmersion`, so this item is formalized as a recall
-- block rather than a redundant wrapper theorem.

/- Lemma 29.20.16: any immersion of schemes is locally quasi-finite. This is a pure canonical
recall: mathlib already provides the instance
`AlgebraicGeometry.instLocallyQuasiFiniteOfIsImmersion`. The Stacks tag evidence is consistent:
item tag `01TN` matches `https://stacks.math.columbia.edu/tag/01TN`. -/
recall AlgebraicGeometry.instLocallyQuasiFiniteOfIsImmersion
