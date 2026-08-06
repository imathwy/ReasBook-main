import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Example_10_1_11

-- Semantic recall via repository precedent: `Topology.CWComplex (Set.univ : Set X)` is the
-- canonical owner for a chosen CW structure. For this construction the relevant local owner is the
-- Chapter 10 source-facing structure `RealProjectiveSpaceStandardCWStructure n`, and the Chapter
-- 13 surface should expose its cell-count companion theorem together with the top attaching-map
-- identification.

/- Construction 13.5.6. This item is a recall of the Chapter 10 construction: the usual CW
structure on `RP^n` is encoded by the source-facing owner
`RealProjectiveSpaceStandardCWStructure n`. Its source-facing companion theorem
`RealProjectiveSpaceStandardCWStructure.spec` records the usual one-cell-per-dimension and
no-higher-cells clauses, and the quotient passage from the antipodal action on `S^n` is exposed by
`realProjectiveSpaceStandardAttachingMapIsDoubleCover`, whose attaching map is
`sphereToRealProjectiveSpace`. -/
#check RealProjectiveSpaceStandardCWStructure
#check RealProjectiveSpaceStandardCWStructure.spec
#check realProjectiveSpaceStandardAttachingMapIsDoubleCover
