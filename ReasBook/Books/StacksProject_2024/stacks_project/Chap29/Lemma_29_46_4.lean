import Mathlib.Tactic.Recall
import StacksProject_2024.Chap29.Lemma_29_45_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

-- Source/core/bridge triage for Lemma 29.46.4:
-- - source-facing: the Stacks statement that a scheme morphism which is a homeomorphism onto a
--   closed subset is affine;
-- - core/canonical: the established Chapter 29 owner
--   `AlgebraicGeometry.isAffineHom_of_base_isClosedEmbedding`;
-- - bridge/view: this item is a direct recall of that owner and should not introduce a second
--   wrapper around the same closed-embedding hypothesis.

/- Lemma 29.46.4: a morphism of schemes that is a homeomorphism onto a closed subset of the target
is affine. This is the direct canonical recall of
`AlgebraicGeometry.isAffineHom_of_base_isClosedEmbedding`. -/
recall AlgebraicGeometry.isAffineHom_of_base_isClosedEmbedding
