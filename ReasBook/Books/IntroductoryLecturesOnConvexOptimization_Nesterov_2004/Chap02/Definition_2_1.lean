import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

variable {α : Type u}
variable (f : α → ℝ) (xStar : α)

/- Definition 2.1: for an objective `f : ℝⁿ → ℝ`, the unconstrained minimization problem
`min_{x ∈ ℝⁿ} f(x)` is the whole-space minimization problem, and a global minimizer is
canonically expressed by `IsMinOn f Set.univ xStar`. The owner itself does not depend on the
ambient `ℝⁿ` presentation, so this file records the generic canonical recall and its textbook
`Set.univ` specialization. -/
recall IsMinOn

recall isMinOn_univ_iff

set_option linter.hashCommand false in
#check
  (show IsMinOn f Set.univ xStar ↔ ∀ x : α, f xStar ≤ f x from
    isMinOn_univ_iff)

end
