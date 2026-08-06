import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Proposition_6_5_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Proposition_6_5_5

-- Semantic recall via `lean_leansearch`: only abstract model-category cofibration results surfaced,
-- so this warning is formalized as a labeled recall block pointing to the chapter-local
-- replacement results already established in Propositions `6.5.3` and `6.5.5`.
/- Warning 6.5.6: the textbook warning is explanatory rather than a new mathematical assertion.
Its content is that the long elementary proofs are used to justify replacing ordinary homotopy
equivalences by equivalences compatible with the relevant cofibration data. In this formalization,
that role is carried by the two source-faithful chapter results below. -/
recall isCofiberHomotopyEquivalence_of_homotopyEquiv
recall isPairHomotopyEquivalence_of_homotopyEquivSquare
