module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Exercise_2_19.EuclideanQuadrant

public section

/- Exercise 2.19 (1). The nonnegative orthant in `EuclideanSpace ℝ (Fin n)` is convex. -/
#check EuclideanQuadrant.convex

/- Exercise 2.19 (2). The nonnegative orthant in `EuclideanSpace ℝ (Fin n)` is closed. -/
#check EuclideanQuadrant.isClosed_nonnegativeOrthant
