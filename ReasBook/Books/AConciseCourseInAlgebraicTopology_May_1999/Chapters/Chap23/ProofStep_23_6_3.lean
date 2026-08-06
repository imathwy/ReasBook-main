import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_3_1

-- Semantic recall via `lean_leansearch` did not surface a more precise owner for the uniqueness
-- step than the existing Chapter 23 declarations
-- `existsUnique_stiefelWhitneyTheory` and
-- `subsingleton_stiefelWhitneyTheory`.

/- Proof step 23.6.3. The uniqueness statement for Stiefel-Whitney classes is already exposed by
the Chapter 23 uniqueness API: `subsingleton_stiefelWhitneyTheory` is the direct equality surface,
and `existsUnique_stiefelWhitneyTheory` packages the same result in canonical `∃!` form. -/
#check existsUnique_stiefelWhitneyTheory
#check subsingleton_stiefelWhitneyTheory
