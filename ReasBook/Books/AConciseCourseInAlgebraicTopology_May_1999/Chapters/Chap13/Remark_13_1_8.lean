import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_2_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Theorem_13_1_7

open AlgebraicTopology

-- Semantic recall via `lean_leansearch`: `singularHomologyFunctor` is the canonical owner for
-- singular homology in mathlib. Local Chapter 13 precedent already provides
-- `restrictPairHomologyTheoryToCWPairs`, `exists_pairHomologyTheory_of_isHomologyTheoryOnCWPairs`,
-- `cellularChainComplex`, and `cellularHomology` as the APIs expressing the functorial
-- CW-approximation viewpoint, the economical CW-level chain model, and its resulting homology.

/- Remark 13.1.8. This item is interpretive rather than a new theorem: singular homology is being
viewed through Theorem 13.1.7 as a particularly functorial passage between homology theories on
all pairs and on CW pairs, while `cellularChainComplex` records the more economical CW-level chain
model and `cellularHomology` its homology. The remark is therefore formalized as a labeled recall
block around those existing owners. -/
#check singularHomologyFunctor
#check restrictPairHomologyTheoryToCWPairs
#check exists_pairHomologyTheory_of_isHomologyTheoryOnCWPairs
#check cellularChainComplex
#check cellularHomology
