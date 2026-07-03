import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_17
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 5.8 is `source-facing`: it records the Chapter 5 smoothness statement for the
concrete log-sum-exp function on Euclidean `ℝ^n`. The smoothness owner is already
`is_l_smooth_on` from Definition 5.1, while the function owner is already Chapter 4's
`log_sum_exp_function : (Fin n → ℝ) → EReal`. This file therefore keeps only the Euclidean
smoothness statement as a `bridge/view` to that earlier owner. -/

recall log_sum_exp_function

-- Proof sketch: compute the Hessian of `fun x ↦ (log_sum_exp_function x).toReal` as
-- `diag(w) - w * wᵀ`, where `w_i = exp (x i) / ∑ k, exp (x k)`. This Hessian is positive
-- semidefinite and bounded above by the identity, so every maximal eigenvalue is at most `1`.
-- Apply the Euclidean Hessian characterization of smoothness for convex functions to conclude
-- global `1`-smoothness.
/-- Proposition 5.8: the log-sum-exp function
`x ↦ log (e^{x_1} + e^{x_2} + ⋯ + e^{x_n})` on Euclidean `ℝ^n` is globally `1`-smooth with
respect to the `l_2` norm. -/
theorem log_sum_exp_l2_function_is_one_smooth (n : ℕ) :
    is_l_smooth_on
      (fun x : EuclideanSpace ℝ (Fin n) ↦ (log_sum_exp_function x).toReal)
      Set.univ 1 := sorry
