module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_32
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_40.Hessian

public section

noncomputable section

namespace Newton

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `IsStep J f s` records the Newton normal equation
`gradient J f + hessian J f s = 0` for the step `s` at the base point `f`. -/
def IsStep (J : H → ℝ) (f s : H) : Prop :=
  gradient J f + hessian J f s = 0

/-- Specification lemma for `Newton.IsStep`. -/
theorem isStep_iff (J : H → ℝ) (f s : H) :
    IsStep J f s ↔ gradient J f + hessian J f s = 0 := by
  -- `IsStep` is defined by the Newton normal equation.
  rfl

end Newton
