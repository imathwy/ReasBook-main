module

public import Book.Ch2.Exercise_2_19.EuclideanQuadrant

public section

/- Example 2.27 (1). The nonnegative orthant in `EuclideanSpace ℝ (Fin n)`, i.e. the set of
vectors `x` with `0 ≤ x i` for each coordinate `i`, is closed. -/
#check EuclideanQuadrant.isClosed_nonnegativeOrthant

/- Example 2.27 (2). The nonnegative orthant in `EuclideanSpace ℝ (Fin n)` is convex. -/
#check EuclideanQuadrant.convex
