import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Theorem_13_1_1

open CategoryTheory.Limits

universe u

-- Local Chapter 13 precedent already packages the axiom on the owner
-- `PairHomologyTheory.additivity`. The source item should therefore stay at the
-- owner/recall layer rather than manufacture a chosen isomorphism witness.

/- Axiom 13.1.5. For a family of pairs `P : ι → SpacePair`, the homology of the disjoint union
pair `SpacePair.sigmaPair P` is isomorphic to the direct sum of the homology groups of the
individual pairs. In this repository the source-facing statement is recorded exactly by the field
`PairHomologyTheory.additivity`, whose conclusion is the existence of such an isomorphism. -/
#check PairHomologyTheory.additivity
#check SpacePair.sigmaPair
