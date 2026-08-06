import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Lemma_8_6_9

-- Semantic recall via repo search: Chapter 8 already contains the source-faithful owner theorem
-- for the actual-fiber to homotopy-fiber comparison, together with its canonical instance
-- companion for typeclass-based reuse.

/- Lemma 9.3.2. The inclusion of the actual fiber `F` into the homotopy fiber `F_p` is already
formalized in Chapter 8 by the based map `actualFiberToHomotopyFiber p`. The source-facing
statement is the theorem owner `actualFiberToHomotopyFiber_isBasedHomotopyEquivalence`, and the
same fact is also available through its canonical instance companion. -/
#check actualFiberToHomotopyFiber_isBasedHomotopyEquivalence
#check actualFiberToHomotopyFiber.instIsCofiberHomotopyEquivalence
