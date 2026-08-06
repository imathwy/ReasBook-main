import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Theorem_13_1_1

-- Semantic recall via `lean_leansearch` did not surface a canonical mathlib owner for the long
-- exact sequence of a Chapter 13 pair homology theory. The local owner `PairHomologyTheory`
-- already records the exactness windows and connecting morphism, so this item is a direct recall
-- of the canonical companion API on that owner.

/- Axiom 13.1.3. The pair long exact sequence is represented in this workspace by the three
exactness-window theorems and the naturality square theorem below on `PairHomologyTheory`. -/
#check PairHomologyTheory.exact_subspace_absoluteToRelative
#check PairHomologyTheory.exact_absoluteToRelative_boundary
#check PairHomologyTheory.exact_boundary_subspace
#check PairHomologyTheory.boundary_naturality
