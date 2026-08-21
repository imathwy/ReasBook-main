module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_17

public section

/- The textbook pseudoinverse notation `K†` is represented in this repository
by the canonical owner `ContinuousLinearMap.pseudoInverse`. When `K` has closed
range, the corresponding source-facing bounded operator is exposed without
extra instance plumbing as `ContinuousLinearMap.pseudoInverseOfClosedRange`. -/
#check ContinuousLinearMap.pseudoInverse
#check ContinuousLinearMap.pseudoInverseOfClosedRange
#check ContinuousLinearMap.isLeastSquaresMinimumNormSolution_pseudoInverseOfClosedRange

/- Exercise 2.11. The source asks to use the open mapping theorem to show that
`K†` is bounded if and only if `K` has closed range.

In this repository, that statement is already formalized canonically by
`ContinuousLinearMap.exists_bounded_pseudoInverse_iff_isClosed_range`. -/
#check ContinuousLinearMap.exists_bounded_pseudoInverse_iff_isClosed_range
