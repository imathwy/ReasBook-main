import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Proposition_4_17
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap05.Definition_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open WithLp (ofLp)

noncomputable section

section

/- Proposition 5.9 is `source-facing`: the textbook object is the concrete log-sum-exp function on
`ℝ^n`, now viewed on the canonical `l_∞` normed model `WithLp ⊤ (Fin n → ℝ)`. Domain sampling:
the Chapter 5 owner predicate is `is_l_smooth_on`, while the existing Chapter 4 owner declaration
for the function itself is `log_sum_exp_function`. This file therefore keeps the source-facing
smoothness statement, but reuses that earlier owner through the canonical coordinate-forgetting map
`ofLp` and `EReal.toReal` instead of introducing a parallel local copy of log-sum-exp. -/

recall log_sum_exp_function

-- Proof sketch: compute the Hessian of `fun x ↦ (log_sum_exp_function (ofLp x)).toReal` as
-- `diag(w) - w wᵀ`, where `w_i = exp (x_i) / ∑ j, exp (x_j)`. For every direction `d`, the
-- associated quadratic form is bounded above by `‖d‖_∞^2`. Then apply the second-order
-- characterization of smoothness to deduce that the Fréchet derivative is globally
-- `1`-Lipschitz.
/-- Proposition 5.9: the log-sum-exp function
`x ↦ log (e^{x_1} + e^{x_2} + ⋯ + e^{x_n})` is globally `1`-smooth with respect to the
`l_∞` norm on `ℝ^n`, modeled as `WithLp ⊤ (Fin n → ℝ)`. -/
theorem log_sum_exp_linfty_function_is_one_smooth (n : ℕ) :
    is_l_smooth_on
      (fun x : WithLp ⊤ (Fin n → ℝ) ↦ (log_sum_exp_function (ofLp x)).toReal)
      Set.univ 1 := sorry

end
