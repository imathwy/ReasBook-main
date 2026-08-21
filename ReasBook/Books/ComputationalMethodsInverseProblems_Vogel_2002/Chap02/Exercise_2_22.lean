module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic

public section

/- Exercise 2.22.

Equation `(2.35)` is the canonical mathlib identity
`DifferentiableAt.lineDeriv_eq_fderiv`: for a differentiable map, the line
derivative in direction `v` equals the Fréchet derivative applied to `v`.

The source-style derivative witness for the one-variable map
`τ ↦ f (x + τ • v)` is the companion bridge `HasFDerivAt.hasLineDerivAt`.
-/

#check DifferentiableAt.lineDeriv_eq_fderiv
#check HasFDerivAt.hasLineDerivAt
