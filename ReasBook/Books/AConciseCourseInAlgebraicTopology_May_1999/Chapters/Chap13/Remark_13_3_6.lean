import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Theorem_13_1_7

-- Local Chapter 13 precedent already fixes `relativeCellularHomology` as the source-facing
-- cellular owner from Definition 13.3.2. The reusable CW-pair axiom package for the dimension,
-- additivity, and excision conclusions mentioned in this remark is the canonical owner
-- `IsHomologyTheoryOnCWPairs` from Theorem 13.1.7, together with its source-facing companion
-- theorem `IsHomologyTheoryOnCWPairs.spec`.

/- Remark 13.3.6. This item is interpretive rather than a new theorem: after Definition 13.3.2
has fixed the relative cellular chain complex and its homology, the dimension, additivity, and
CW-excision axioms referred to here live on the canonical CW-pair homology-theory owner from
Theorem 13.1.7. The remark is therefore formalized as a labeled recall block around the source
relative cellular homology object and that canonical CW-pair owner surface. -/
#check relativeCellularHomology
#check IsHomologyTheoryOnCWPairs
#check IsHomologyTheoryOnCWPairs.spec
