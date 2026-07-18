import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Algorithm_8_13
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Assumption_8_38
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Definition_8_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ}
variable {fi : Fin m → E → EReal} {C XStar : Set E} {fOpt Θ : ℝ}
variable (h_problem : IsConstrainedConvexProblem (finite_sum_objective fi) C XStar fOpt)
variable (h_incremental : IncrementalProjectedSubgradientAssumptions fi C)
variable (g : ℕ → C → Fin m → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  incremental_projected_subgradient_method
    C h_problem.feasible_nonempty h_problem.feasible_closed h_problem.feasible_convex t g x0 k

local notation "x[" k "," i "]" =>
  incremental_projected_subgradient_inner_iterate
    C h_problem.feasible_nonempty h_problem.feasible_closed h_problem.feasible_convex t g k x[k] i

-- Proof sketch: apply Lemma 8.39 to an arbitrary optimal point `xStar ∈ XStar`, sum the
-- fundamental inequality from `0` through `k`, and use the defining minimality of
-- `best_achieved_function_value` to obtain the standard estimate
-- `(f_best^k - fOpt) ≤ (‖x0 - xStar‖² + L² m² ∑_{n ≤ k} t_n²) / (2 ∑_{n ≤ k} t_n)`. The ratio
-- hypothesis forces the error term to vanish, while positivity of the stepsizes makes the
-- denominator diverge.
/-- Theorem 8.40 (1): clause (a). Under Assumptions 8.7 and 8.38, if the incremental projected
subgradient method uses positive stepsizes and the ratio
`(∑_{n=0}^k t_n^2) / (∑_{n=0}^k t_n)` tends to `0`, then the best objective gap attained by the
first `k + 1` iterates converges to `0`. -/
theorem incremental_projected_subgradient_best_value_gap_tendsto_zero_of_stepsize_ratio
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) (x[k,i] : E))
    (h_stepsize_pos : ∀ n, 0 < t n)
    (h_ratio :
      Filter.Tendsto
        (fun k ↦
          (Finset.sum (Finset.range (k + 1)) fun n ↦ (t n) ^ (2 : ℕ)) /
            Finset.sum (Finset.range (k + 1)) fun n ↦ t n)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k ↦
        best_achieved_function_value
            (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
            (fun n ↦ (x[n] : E)) k -
          fOpt)
      Filter.atTop (nhds 0) := sorry

-- Proof sketch: sum the inequality from Lemma 8.39 over the tail indices `⌊k / 2⌋, …, k`,
-- control the telescoping distance term by the half-squared-diameter bound `Θ`, substitute the
-- explicit stepsize `t_n = √Θ / (L m √(n + 1))`, and then apply Lemma 8.27 (2) with `D = 2`.
/-- Theorem 8.40 (2): clause (b). If `Θ` bounds the half squared diameter of the feasible set `C`
and the incremental projected subgradient method uses the stepsizes
`t_k = √Θ / (L m √(k + 1))`, where `L = h_incremental.L`, then for every `k ≥ 2` the best
objective gap satisfies
`f_best^k - fOpt ≤ 2 (2 + log 3) m L √Θ / √(k + 2)`. The compactness hypothesis from the prose is
omitted because the explicit bound `Θ` is the actual datum used in the estimate. -/
theorem incremental_projected_subgradient_best_value_gap_le_of_half_squared_diameter_stepsize
    (hm : 0 < m)
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) (x[k,i] : E))
    (hΘ :
      ∀ x ∈ C, ∀ y ∈ C, (1 / 2 : ℝ) * ‖x - y‖ ^ (2 : ℕ) ≤ Θ)
    (h_stepsize :
      ∀ n,
        t n = Real.sqrt Θ /
          (h_incremental.L * (m : ℝ) * Real.sqrt ((n : ℝ) + 1)))
    {k : ℕ} (hk : 2 ≤ k) :
    best_achieved_function_value
        (fun y : E ↦ ((finite_sum_objective fi) y).toReal)
        (fun n ↦ (x[n] : E)) k -
      fOpt ≤
      (2 * (2 + Real.log 3)) * (m : ℝ) * h_incremental.L * Real.sqrt Θ /
        Real.sqrt ((k : ℝ) + 2) := sorry

end
