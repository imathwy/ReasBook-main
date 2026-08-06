import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: the source-facing `HasSphereConeHelp n e` bridge to this canonical two-degree
-- owner is provided by `Lemma_9_6_6`; this proof step itself is the surjectivity half of that
-- owner.
/- ProofStep 9.6.8: the surjectivity conclusion is the `surjectiveSucc` field of the canonical
two-degree homotopy-group owner `HasPiInjectiveSurjectiveSucc n e`, and Lemma 9.6.6 identifies
that owner with the HELP condition `HasSphereConeHelp n e`. -/
recall HasPiInjectiveSurjectiveSucc.surjectiveSucc
