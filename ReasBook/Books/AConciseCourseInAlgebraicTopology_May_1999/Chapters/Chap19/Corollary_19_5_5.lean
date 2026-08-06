import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_1_5

universe u

/-
Corollary 19.5.5: Theorem 19.5.4 identifies ordinary cohomology on CW pairs with cellular
cochains, and hence ordinary cohomology with coefficients in `π` is uniquely determined on all
pairs by the Chapter 18 axioms. The canonical all-pairs uniqueness owner is
`pairCohomologyTheory_unique`.

Recall from Theorem 19.5.4: on CW pairs, the comparison is packaged by
`exists_relativeCellularCochainComparison`.
-/

/-- Corollary 19.5.5: ordinary cohomology is uniquely determined by the axioms, just as ordinary
homology is. Concretely, any two Chapter 18 pair cohomology theories with coefficients in `π`
are uniquely determined up to isomorphism. -/
theorem pairCohomologyTheory_unique
    {π : Type u} [AddCommGroup π] (H K : PairCohomologyTheory π) :
    Nonempty (PairCohomologyTheory.Iso H K) := sorry
