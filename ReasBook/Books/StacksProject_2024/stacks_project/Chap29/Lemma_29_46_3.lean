import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap29.Lemma_29_45_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

-- Source/core/bridge triage for Lemma 29.46.3:
-- - source-facing: the Stacks statement that a composite of universal homeomorphisms is again a
--   universal homeomorphism;
-- - core/canonical: the established Chapter 29 owner `UniversalHomeomorphism`, with the
--   source-facing composition theorem `universalHomeomorphism_comp` already provided by
--   `Lemma_29_45_3`;
-- - bridge/view: this item is a direct recall of that established theorem and should not
--   introduce a duplicate local wrapper.

/- Lemma 29.46.3: the composition of universal homeomorphisms of schemes is a universal
homeomorphism. This is a pure canonical recall of
`AlgebraicGeometry.universalHomeomorphism_comp`. -/
recall AlgebraicGeometry.universalHomeomorphism_comp
