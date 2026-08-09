module

public import TR_LALM_theory.Assumption_2_3.Parameters

public section

namespace LALM

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- The coefficient controlling the contribution of stochastic gradient error
to successive multiplier differences. -/
@[expose]
noncomputable def multiplierErrorConstant (h : EqualityConstrained.Regularity f c) : ℝ :=
  4 / h.licqModulus ^ 2

/-- The multiplier-error constant has its defining explicit formula. -/
theorem multiplierErrorConstant_def (h : EqualityConstrained.Regularity f c) :
    multiplierErrorConstant h = 4 / h.licqModulus ^ 2 := rfl

end LALM

end
