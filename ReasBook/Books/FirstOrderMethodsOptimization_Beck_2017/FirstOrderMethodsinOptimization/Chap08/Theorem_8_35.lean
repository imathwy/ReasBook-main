import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Assumption_8_34
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Proposition_3_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open MeasureTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

section

variable {E : Type u} {Ω : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [MeasurableSpace E] [BorelSpace E]
variable {f : E → ℝ} {C XStar : Set E} {fOpt Θ : ℝ}
variable (h_problem : IsConstrainedConvexProblem (fun x : E ↦ (f x : EReal)) C XStar fOpt)
variable (x : ℕ → Ω → C) (g : ℕ → Ω → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  x k

/- Theorem 8.35 is `source-facing`: it gives convergence and the `O(1 / √k)` rate for the
expected running-best objective value along the concrete stochastic projected subgradient
iterates. The canonical owners already present in Chapter 8 are the running minimum
`best_achieved_function_value`, the standing problem class `IsConstrainedConvexProblem`, and the
stochastic oracle package `StochasticProjectedSubgradientOracle`. The theorem therefore records the
generated iterates directly as a pathwise family `x : ℕ → Ω → C` together with the textbook
projected-update recurrence. -/

-- Proof sketch: apply the stochastic one-step descent inequality obtained from the projection
-- nonexpansiveness and the oracle assumptions to an optimal point `xStar ∈ XStar`, then sum from
-- `0` to `k` and use the prefix-minimality of `best_achieved_function_value` to get
-- `μ[f_best^k] - fOpt ≤ (D + L_tilde_f^2 * ∑_{n ≤ k} t_n^2) / (2 * ∑_{n ≤ k} t_n)`.
-- The hypothesis that `(∑ t_n^2) / (∑ t_n) → 0` forces the right-hand side to converge to `0`.
/-- Theorem 8.35 (1): under Assumptions 8.7 and 8.34, if the stochastic projected subgradient
method uses positive stepsizes and
`(∑_{n=0}^k t_n^2) / (∑_{n=0}^k t_n) → 0`, then the expected best objective value attained by the
first `k + 1` stochastic iterates converges to the optimal value `fOpt`. -/
theorem stochastic_projected_subgradient_expected_best_value_tendsto_of_stepsize_ratio
    (h_zero : ∀ ω, x[0] ω = x0)
    (h_succ :
      ∀ k ω,
        x[k + 1] ω =
          metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed.isComplete
            h_problem.feasible_convex ((x[k] ω : E) - t k • g k ω))
    (h_stepsize_pos : ∀ n, 0 < t n)
    (h_oracle :
      StochasticProjectedSubgradientOracle μ f
        (fun k ω ↦ (x[k] ω : E))
        g)
    (h_ratio :
      Filter.Tendsto
        (fun k ↦
          (Finset.sum (Finset.range (k + 1)) fun n ↦ (t n) ^ (2 : ℕ)) /
            Finset.sum (Finset.range (k + 1)) fun n ↦ t n)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k ↦
        μ[fun ω ↦
          best_achieved_function_value f (fun n ↦ (x[n] ω : E)) k])
      Filter.atTop (nhds fOpt) := sorry

-- Proof sketch: sum the stochastic descent inequality from `⌈k / 2⌉` through `k`, use the
-- half-squared-diameter bound `Θ` to control the distance term because every iterate and every
-- optimal point lie in `C`, then substitute the stepsize
-- `t_n = √(2 Θ) / (L_tilde_f √(n + 1))`. The resulting ratio of a harmonic tail to an
-- inverse-square-root tail is bounded by Lemma 8.27 (2), giving the constant `2 * (1 + log 3)`.
/-- Theorem 8.35 (2): under Assumptions 8.7 and 8.34, if `Θ` bounds the half squared diameter of
`C` and the stochastic projected subgradient method uses the stepsizes
`t_k = √(2 Θ) / (L_tilde_f √(k + 1))`, then for every `k ≥ 2` the expected best objective gap
satisfies
`E[f_best^k] - fOpt ≤ 2 (1 + log 3) L_tilde_f √(2 Θ) / √(k + 2)`. -/
theorem stochastic_projected_subgradient_expected_best_value_gap_le_of_half_squared_diameter_stepsize
    (h_zero : ∀ ω, x[0] ω = x0)
    (h_succ :
      ∀ k ω,
        x[k + 1] ω =
          metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed.isComplete
            h_problem.feasible_convex ((x[k] ω : E) - t k • g k ω))
    (h_stepsize_pos : ∀ n, 0 < t n)
    (h_oracle :
      StochasticProjectedSubgradientOracle μ f
        (fun k ω ↦ (x[k] ω : E))
        g)
    (hΘ :
      ∀ x ∈ C, ∀ y ∈ C, (1 / 2 : ℝ) * ‖x - y‖ ^ (2 : ℕ) ≤ Θ)
    (h_stepsize :
      ∀ n,
        t n = Real.sqrt (2 * Θ) / (h_oracle.L_tilde_f * Real.sqrt ((n : ℝ) + 1)))
    {k : ℕ} (hk : 2 ≤ k) :
    μ[fun ω ↦ best_achieved_function_value f (fun n ↦ (x[n] ω : E)) k] - fOpt ≤
      (2 * (1 + Real.log 3)) * h_oracle.L_tilde_f * Real.sqrt (2 * Θ) /
        Real.sqrt ((k : ℝ) + 2) := sorry

end
