import FirstOrderMethodsinOptimization.Chap08.Theorem_8_35

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
variable {f : E → ℝ} {C XStar : Set E} {fOpt δ Θ : ℝ} {m : ℕ}
variable (L : Fin m → ℝ)
variable (h_problem : IsConstrainedConvexProblem (fun x : E ↦ (f x : EReal)) C XStar fOpt)
variable (x : ℕ → Ω → C) (g : ℕ → Ω → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  x k

/- Proposition 8.8 is `bridge/view`: it specializes the general stochastic projected-subgradient
rate from Theorem 8.35 to the finite-sum setting through an explicit bound
`L_tilde_f ≤ δ * √m * √(∑ i, L_{f_i}^2)`. The owner abstractions remain the Chapter 8 running-best
value `best_achieved_function_value`, the standing projected-subgradient problem class, and the
stochastic oracle package; the finite-sum data enter only through the component Lipschitz
constants `L i`. -/

-- Proof sketch: apply Theorem 8.35 (2) to the stochastic projected-subgradient iterates with the
-- prescribed stepsize `t_k = √(2 Θ) / (L_tilde_f √(k + 1))`. Then substitute the finite-sum
-- estimate `L_tilde_f ≤ δ * √m * √(∑ i, L i^2)` into the resulting right-hand side.
/-- Proposition 8.8: if the stochastic projected subgradient oracle along `x^k` has bound constant
`L_tilde_f` controlled by `δ * √m * √(∑ i, L_{f_i}^2)`, then the expected best objective gap of the
first `k + 1` iterates satisfies the finite-sum `O(1 / √k)` estimate
`E(f_best^k) - fOpt ≤ δ √m √(∑ i, L_{f_i}^2) √(2 Θ) / √(k + 2)`. -/
theorem stochastic_projected_subgradient_expected_best_value_gap_le_of_finite_sum_bound
    (h_zero : ∀ ω, x[0] ω = x0)
    (h_succ :
      ∀ k ω,
        x[k + 1] ω =
          metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed.isComplete
            h_problem.feasible_convex ((x[k] ω : E) - t k • g k ω))
    (h_stepsize_pos : ∀ n, 0 < t n)
    (h_oracle :
      StochasticProjectedSubgradientOracle μ f
        (fun n ω ↦ (x[n] ω : E))
        g)
    (hΘ :
      ∀ y ∈ C, ∀ z ∈ C, (1 / 2 : ℝ) * ‖y - z‖ ^ (2 : ℕ) ≤ Θ)
    (h_stepsize :
      ∀ n,
        t n = Real.sqrt (2 * Θ) / (h_oracle.L_tilde_f * Real.sqrt ((n : ℝ) + 1)))
    (h_oracle_bound :
      (2 * (1 + Real.log 3)) * h_oracle.L_tilde_f ≤
        δ * Real.sqrt (m : ℝ) * Real.sqrt (∑ i : Fin m, L i ^ (2 : ℕ)))
    (k : ℕ) (hk : 2 ≤ k) :
    μ[fun ω ↦ best_achieved_function_value f (fun n ↦ (x[n] ω : E)) k] - fOpt ≤
      δ * Real.sqrt (m : ℝ) * Real.sqrt (∑ i : Fin m, L i ^ (2 : ℕ)) *
        Real.sqrt (2 * Θ) / Real.sqrt ((k : ℝ) + 2) := sorry

-- Proof sketch: first apply
-- `stochastic_projected_subgradient_expected_best_value_gap_le_of_finite_sum_bound` to obtain the
-- bound `δ * √m * √(∑ i, L i^2) * √(2 Θ) / √(k + 2)` on the expected best objective gap. Then use
-- the lower bound on `k` to rearrange this rate estimate into an upper bound by `ε`.
/-- If the iteration index is at least the finite-sum complexity threshold from Proposition 8.8,
then the expected best objective gap is at most `ε`. -/
theorem stochastic_projected_subgradient_expected_best_value_gap_le_epsilon_of_finite_sum_iteration_count
    (h_zero : ∀ ω, x[0] ω = x0)
    (h_succ :
      ∀ k ω,
        x[k + 1] ω =
          metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed.isComplete
            h_problem.feasible_convex ((x[k] ω : E) - t k • g k ω))
    (h_stepsize_pos : ∀ n, 0 < t n)
    (h_oracle :
      StochasticProjectedSubgradientOracle μ f
        (fun n ω ↦ (x[n] ω : E))
        g)
    (hΘ :
      ∀ y ∈ C, ∀ z ∈ C, (1 / 2 : ℝ) * ‖y - z‖ ^ (2 : ℕ) ≤ Θ)
    (h_stepsize :
      ∀ n,
        t n = Real.sqrt (2 * Θ) / (h_oracle.L_tilde_f * Real.sqrt ((n : ℝ) + 1)))
    (h_oracle_bound :
      (2 * (1 + Real.log 3)) * h_oracle.L_tilde_f ≤
        δ * Real.sqrt (m : ℝ) * Real.sqrt (∑ i : Fin m, L i ^ (2 : ℕ)))
    (hδ : 0 ≤ δ) (hΘ_nonneg : 0 ≤ Θ)
    {ε : ℝ} (hε : 0 < ε)
    (k : ℕ)
    (hk :
      max
          (δ ^ (2 : ℕ) * (m : ℝ) * (2 * Θ) * (∑ i : Fin m, L i ^ (2 : ℕ)) /
              ε ^ (2 : ℕ) - 2)
          2 ≤
        (k : ℝ)) :
    μ[fun ω ↦ best_achieved_function_value f (fun n ↦ (x[n] ω : E)) k] - fOpt ≤ ε := sorry

end
