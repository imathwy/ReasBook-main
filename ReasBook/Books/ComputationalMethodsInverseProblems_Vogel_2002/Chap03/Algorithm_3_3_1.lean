module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Algorithm_3_3_1.Run

public section

/- Algorithm 3.3.1. BFGS Method with Line Search.

The source variables `f_v`, `g_v`, and `H_v` are bundled as `σ v :
BFGS.State`. The source direction `p_(v+1)` is represented by
`BFGS.direction (σ v) ...`, and the source line-search minimizer `τ_(v+1)` is
represented by the step-indexed scalar `τ v`. The reusable run owner is
`BFGS.IsRun`. -/
#check BFGS.IsRun
