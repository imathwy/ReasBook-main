import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_1_1

open CategoryTheory

universe u

-- Semantic recall via `lean_leansearch` surfaced only unrelated group-cohomology connecting-map
-- APIs. Local Chapter 18 precedent already packages the source statement by the field
-- `PairCohomologyTheory.boundary` together with the source-facing exactness window
-- `PairCohomologyTheory.exact_subspaceInclusion_boundary`.

/- Axiom 18.1.2. The source statement is the direction convention for the connecting morphism in
the cohomology long exact sequence: for a pair `P = (X, A)` and degree `q`, evaluating
`PairCohomologyTheory.boundary q` at `P` gives the morphism
`H^q(A; π) ⟶ H^(q + 1)(X, A; π)`, so cohomological exactness reverses the arrow direction from
the homological case. -/
#check PairCohomologyTheory.boundary
#check PairCohomologyTheory.exact_subspaceInclusion_boundary
