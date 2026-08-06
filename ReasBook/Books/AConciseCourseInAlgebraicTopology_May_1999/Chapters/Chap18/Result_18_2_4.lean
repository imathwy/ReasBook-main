import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_1_5

-- Result 18.2.4 is already formalized by the Chapter 18 owner for the reversed connecting
-- morphism, the induced CW-pair cohomology-theory instance, and the extension theorem from CW
-- pairs to all pairs. The bundled extension theorem is the repository-facing companion used by
-- later files.

/- Result 18.2.4. The current formalization already records the cohomological verification of the
axioms, with the homological arrows reversed, by the Chapter 18 owner for the connecting
morphism together with the theorems packaging the induced CW-pair cohomology axioms and their
extension to all pairs. This result is therefore recorded as a labeled recall block around those
existing declarations and the bundled extension companion. -/
#check PairCohomologyTheory.boundary
#check restrictPairCohomologyTheoryToCWPairs_isCohomologyTheoryOnCWPairs
#check exists_pairCohomologyTheory_of_isCohomologyTheoryOnCWPairs
#check exists_pairCohomologyTheory_of_cwPairCohomologyTheory
