import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Calculation_18_4_1

-- Chapter 18 already records the faithful local owner
-- `IsRealProjectiveSpaceModTwoCohomologyTruncatedPolynomialPresentation` on
-- `Hˢ[q](TopCat.of (RealProjectiveSpace n); ZMod 2)`, so this corollary reuses that owner
-- directly rather than rebuilding the same package with a redundant vanishing clause.

/- Corollary 20.1.8. The mod-`2` cohomology ring `H^*(RP^n; ZMod 2)` is
`ZMod 2[α] / (α^(n + 1))` with `|α| = 1`. On the Chapter 18 cohomology owner
`realProjectiveSpaceModTwoCohomology n q`, this is exactly the source-facing existence theorem
`realProjectiveSpace_modTwoCohomologyRing_generatedByDegreeOne`. -/
#check realProjectiveSpace_modTwoCohomologyRing_generatedByDegreeOne
