module

public import ComputationalMethodsInverseProblems_Vogel_2002.Book.Ch3.Theorem_3_11

public section

/- Exercise 3.9. The chapter's significant-digits consequence of the quadratic
estimate `(3.19)` is supported by the canonical Newton theorem
`Newton.newtonConvergesWithQuadraticEstimate`, which packages both convergence
to `fStar` and the estimate
`‖f (v + 1) - fStar‖ ≤ cStar J fStar γ * ‖f v - fStar‖ ^ 2`. -/
#check Newton.newtonConvergesWithQuadraticEstimate
