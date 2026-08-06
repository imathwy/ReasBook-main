import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_3_4

-- Semantic recall via `lean_leansearch` surfaced only general graded-ring infrastructure, not a
-- more canonical singular-cohomology ring owner for the current Chapter 18 development. Local
-- precedent from `Theorem_18_3_4` already packages the source remark by the quotient-level cup
-- product, its unit class, and the associated naturality, unit, associativity, and
-- graded-commutativity laws.

/- Remark 18.3.5. Cup products make cohomology more informative than homology by encoding
multiplicative structure. In the current formalization, this extra structure is recorded by the
quotient-level cup product on singular cohomology together with its unit class and its
naturality, left/right unit, associativity, and graded-commutativity laws from
`Theorem_18_3_4`. -/
#check singularCohomologyClasses.cup
#check singularCohomologyOneClass
#check singularCohomologyCup_naturality
#check singularCohomologyCup_left_unit
#check singularCohomologyCup_right_unit
#check singularCohomologyCup_assoc
#check singularCohomologyCup_gradedComm
