module

public import ComputationalMethodsInverseProblems_Vogel_2002.Book.Ch3.Definition_3_2
public import Mathlib.Analysis.Calculus.ContDiff.Defs

public section

noncomputable section

namespace LineSearch

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Exercise 3.2. If `J` is continuously differentiable and condition `(3.6)`
holds in the form `inner ℝ (gradient J f_v) p_v < 0`, then `p_v` is a descent
direction for `J` at `f_v`. -/
theorem isDescentDirection_of_contDiff_inner_gradient_neg {J : H → ℝ} {f_v p_v : H}
    (hJ : ContDiff ℝ 1 J) (h36 : inner ℝ (gradient J f_v) p_v < 0) :
    IsDescentDirection J f_v p_v :=
  isDescentDirection_of_inner_gradient_neg hJ.contDiffAt.differentiableAt_one h36

end LineSearch
