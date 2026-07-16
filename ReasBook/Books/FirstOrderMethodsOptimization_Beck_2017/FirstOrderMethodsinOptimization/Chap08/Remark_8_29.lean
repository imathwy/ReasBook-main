import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Theorem_8_28

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped BigOperators

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → EReal} {C XStar : Set E} {fOpt : ℝ}
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (h_bound : SubgradientNormBoundOn f C)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k

/-- The partial sums `T_k = ∑_{n=0}^k t_n` of the projected-subgradient stepsizes. -/
def projected_subgradient_stepsize_prefix_sum (t : ℕ → ℝ) (k : ℕ) : ℝ :=
  Finset.sum (Finset.range (k + 1)) fun n ↦ t n

-- Proof sketch: split the sum over `Finset.range (k + 2)` into the prefix
-- `Finset.range (k + 1)` and the last term `k + 1`.
/-- The stepsize prefix sums satisfy `T_{k+1} = T_k + t_{k+1}`. -/
theorem projected_subgradient_stepsize_prefix_sum_succ (k : ℕ) :
    projected_subgradient_stepsize_prefix_sum t (k + 1) =
      projected_subgradient_stepsize_prefix_sum t k + t (k + 1) := sorry

/-- Remark 8.29: for the projected subgradient method with dynamic stepsizes
`t_k = 1 / (‖f'(x^k)‖ √(k + 1))` when the chosen direction is nonzero and `t_k = 1 / L_f`
otherwise, the weighted averages from Theorem 8.28 satisfy the recursion
`x^(k+1) = (T_k / T_{k+1}) x^(k) + (t_{k+1} / T_{k+1}) x^(k+1)`, where
`T_k = ∑_{n=0}^k t_n`. -/
-- Proof sketch: first use the dynamic stepsize formulas and `h_bound.L_f_pos` to show each
-- `t_n` is positive, hence both `T_k` and `T_{k+1}` are nonzero. Then unfold
-- `projected_subgradient_stepsize_average_iterate` at `k` and `k + 1`, split the sum defining
-- `x^(k+1)` into the prefix through `k` and the last term, and rewrite the prefix using
-- `projected_subgradient_stepsize_prefix_sum` and
-- `projected_subgradient_stepsize_average_iterate`.
theorem projected_subgradient_stepsize_average_iterate_succ
    (h_stepsize_zero :
      ∀ n, g n (x[n]) = 0 → t n = 1 / h_bound.L_f)
    (h_stepsize_nonzero :
      ∀ n,
        g n (x[n]) ≠ 0 →
          t n = 1 / (‖g n (x[n])‖ * Real.sqrt ((n : ℝ) + 1)))
    (k : ℕ) :
    projected_subgradient_stepsize_average_iterate h_problem g t x0 (k + 1) =
      (projected_subgradient_stepsize_prefix_sum t k /
          projected_subgradient_stepsize_prefix_sum t (k + 1)) •
        projected_subgradient_stepsize_average_iterate h_problem g t x0 k +
      (t (k + 1) / projected_subgradient_stepsize_prefix_sum t (k + 1)) • (x[k + 1] : E) := sorry

end
