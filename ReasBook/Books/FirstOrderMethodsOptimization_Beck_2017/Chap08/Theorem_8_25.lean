import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_3
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → EReal} {C XStar : Set E} {fOpt : ℝ}
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k

/- Theorem 8.25 is `source-facing`: it is the convergence criterion for the concrete projected
subgradient iterates under a general positive stepsize rule. The canonical owners already present
in the chapter are the recursive iterate sequence `projected_subgradient_method`, the running-best
objective owner `best_achieved_function_value`, the standing problem assumptions
`IsConstrainedConvexProblem`, and the subgradient bound package `SubgradientNormBoundOn`.
Accordingly, the theorem is stated directly in terms of those owners and the textbook's ratio
condition on the partial sums of `t_k` and `t_k^2`, without introducing a surrogate wrapper for
dynamic stepsize schedules. -/

-- Proof sketch: apply Lemma 8.24 to an arbitrary optimal point `xStar ∈ XStar`, then use the
-- uniform bound from `h_bound` and the prefix-minimality of `best_achieved_function_value` to
-- derive
-- `f_best^k - fOpt ≤ ‖x0 - xStar‖^2 / (2 ∑_{n ≤ k} t_n) +
--   h_bound.L_f^2 * (∑_{n ≤ k} t_n^2) / (2 ∑_{n ≤ k} t_n)`.
-- The hypothesis on the ratio of partial sums forces the second term to vanish, and positivity of
-- the stepsizes implies `∑_{n ≤ k} t_n → ∞`, so the first term also tends to `0`.
/-- Theorem 8.25: under Assumptions 8.7 and 8.12, if the projected subgradient method uses
positive stepsizes and the ratio
`(∑_{n=0}^k t_n^2) / (∑_{n=0}^k t_n)` tends to `0`, then the best objective value achieved by the
first `k + 1` iterates converges to the optimal value `fOpt`. -/
theorem projected_subgradient_method_best_value_gap_tendsto_zero_of_stepsize_ratio
    (h_bound : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_stepsize_pos : ∀ n, 0 < t n)
    (h_ratio :
      Filter.Tendsto
        (fun k ↦
          (Finset.sum (Finset.range (k + 1)) fun n ↦ (t n) ^ (2 : ℕ)) /
            Finset.sum (Finset.range (k + 1)) fun n ↦ t n)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k ↦
        best_achieved_function_value (fun y : E ↦ (f y).toReal) (fun n ↦ (x[n] : E)) k - fOpt)
      Filter.atTop (nhds 0) := sorry

end
