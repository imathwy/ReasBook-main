module

public import Book.Ch4.Definition_4_34.MinimumVarianceLinear

public section

/- Definition 4.34. The minimum variance linear estimator of `X` from `Z` is formalized by
`ProbabilityTheory.MinimumVarianceLinear.IsEstimator`, with
`ProbabilityTheory.MinimumVarianceLinear.isEstimator_iff` exposing the optimal-coefficient view
under the finite-second-moment hypotheses. -/
#check ProbabilityTheory.MinimumVarianceLinear.IsEstimator
#check ProbabilityTheory.MinimumVarianceLinear.isEstimator_iff
