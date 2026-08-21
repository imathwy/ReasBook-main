module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_40.Hessian

public section

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Definition 2.40. If `J` is Fréchet differentiable on a neighborhood of `f` with derivative
`fderiv ℝ J` and this derivative map has a Fréchet derivative at `f`, then the second Fréchet
derivative is represented by the bounded operator `hessian J f` through
`fderiv ℝ (fderiv ℝ J) f h k = inner ℝ (hessian J f h) k`. -/
theorem hessianRepresentation (J : H → ℝ) (f h k : H) :
    fderiv ℝ (fderiv ℝ J) f h k = inner ℝ (hessian J f h) k :=
  (hessian_inner J f h k).symm
