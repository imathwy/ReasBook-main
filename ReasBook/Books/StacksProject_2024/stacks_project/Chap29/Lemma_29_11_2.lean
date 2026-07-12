import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: mathlib already exposes the exact source-facing consequences of affine
-- morphisms through `AlgebraicGeometry.IsSeparated.of_isAffineHom` and the instance
-- `AlgebraicGeometry.instQuasiCompactOfIsAffineHom`, so this file should use those canonical
-- owners directly rather than restating them as duplicate local theorems.

/- Lemma 29.11.2 (1): an affine morphism is separated. This is the canonical mathlib theorem
`AlgebraicGeometry.IsSeparated.of_isAffineHom`. -/
recall AlgebraicGeometry.IsSeparated.of_isAffineHom

/- Lemma 29.11.2 (2): an affine morphism is quasi-compact. This is the canonical mathlib
instance `AlgebraicGeometry.instQuasiCompactOfIsAffineHom`. -/
recall AlgebraicGeometry.instQuasiCompactOfIsAffineHom
