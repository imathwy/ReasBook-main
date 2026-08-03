module

public import Mathlib.LinearAlgebra.AffineSpace.Independent

/- Definition 50.4: Munkres's geometrically independent, or affinely independent,
family `x : Fin (k + 1) → EuclideanSpace ℝ (Fin N)` is mathlib's
`AffineIndependent ℝ x`; the finite-family coefficient criterion is given by
`affineIndependent_iff_of_fintype`. -/
#check AffineIndependent
#check affineIndependent_iff_of_fintype
