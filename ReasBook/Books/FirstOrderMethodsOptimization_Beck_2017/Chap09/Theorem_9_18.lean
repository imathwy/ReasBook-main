import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_1
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f ω : E → EReal} {C XStar : Set E} {fOpt σ : ℝ}
variable {x g : ℕ → E} {t : ℕ → ℝ}

/- `prompt_add/` is absent in this workspace, so the API review is based on the existing Chapter 8
and Chapter 9 owner files. Theorem 9.18 is `source-facing`: it states the asymptotic convergence
and the dynamic-step `O(log k / √k)` rate for a concrete mirror-descent trajectory under the
standing constrained-problem assumptions of Definition 9.1 and the Bregman-potential assumptions of
Definition 9.2. The canonical owners already present are `IsConstrainedConvexProblem`,
`IsBregmanPotentialOn`, `SubgradientNormBoundOn`, `is_mirror_descent_trajectory`,
`best_achieved_function_value`, and `B[ω]`. -/

-- Proof sketch: apply the running-best estimate from Lemma 9.14 with the bound constant
-- `h_bound.L_f`. The right-hand side becomes
-- `B_ω(xStar, x⁰) / ∑_{n ≤ k} t_n + (h_bound.L_f^2 / (2σ)) * (∑_{n ≤ k} t_n^2 / ∑_{n ≤ k} t_n)`
-- for an optimal point `xStar ∈ XStar`. Since `xStar` is fixed, the first term is negligible and
-- the hypothesis `h_ratio` forces the second term to converge to `0`, so the running-best value
-- tends to `fOpt`.
/-- Theorem 9.18 (1): under the standing constrained mirror-descent assumptions of Definitions 9.1
and 9.2, if every subgradient of `f` on `C` has norm at most `L_f = h_bound.L_f` and
`(∑_{n=0}^k t_n^2) / (∑_{n=0}^k t_n) → 0`, then the running-best objective value attained by the
mirror-descent iterates converges to the optimal value `fOpt`. -/
theorem mirror_descent_best_value_tendsto_of_stepsize_ratio
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (h_bound : SubgradientNormBoundOn f C)
    (h_traj :
      is_mirror_descent_trajectory (fun y : E ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (h_ratio :
      Filter.Tendsto
        (fun k ↦
          (Finset.sum (Finset.range (k + 1)) fun n ↦ (t n) ^ (2 : ℕ)) /
            (Finset.sum (Finset.range (k + 1)) fun n ↦ t n))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k ↦ best_achieved_function_value (fun y : E ↦ (f y).toReal) x k)
      Filter.atTop (nhds fOpt) := sorry

-- Proof sketch: use the running-best estimate from Lemma 9.14 and
-- substitute the predefined stepsize `t n = √(2σ) / (L_f √(n + 1))`. This gives
-- `(t n)^2 * ‖g n‖^2 ≤ 2σ / (n + 1)` from the uniform norm bound `‖g n‖ ≤ L_f`. The numerator
-- then becomes
-- `B_ω(xStar, x⁰) + ∑_{n ≤ k} 1 / (n + 1)`, the denominator is bounded below by
-- `(√(2σ) / L_f) * ∑_{n ≤ k} 1 / √(n + 1)`, and Lemma 8.27 (1) gives the stated
-- `O(log k / √k)` bound.
/-- Theorem 9.18 (2): under the standing constrained mirror-descent assumptions of Definitions 9.1
and 9.2, if the mirror-descent stepsizes are chosen by the predefined diminishing rule
`t_k = √(2σ) / (L_f √(k + 1))`, then for every optimal point `xStar ∈ XStar` and every `k ≥ 1`
the running-best objective gap satisfies the standard
`(L_f / √(2σ)) * (B_ω(xStar, x⁰) + 1 + log (k + 1)) / √(k + 1)` estimate. -/
theorem mirror_descent_best_value_gap_le_log_over_sqrt_of_predefined_diminishing_stepsizes
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (h_bound : SubgradientNormBoundOn f C)
    (h_traj :
      is_mirror_descent_trajectory (fun y : E ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    {k : ℕ} (hk : 1 ≤ k)
    (h_stepsize :
      ∀ n, t n = Real.sqrt (2 * σ) / (h_bound.L_f * Real.sqrt ((n : ℝ) + 1))) :
    best_achieved_function_value (fun y : E ↦ (f y).toReal) x k - fOpt ≤
      (h_bound.L_f / Real.sqrt (2 * σ)) *
        (B[ω] xStar (x 0) + 1 + Real.log ((k : ℝ) + 1)) /
        Real.sqrt ((k : ℝ) + 1) := sorry

-- Proof sketch: use the running-best estimate from Lemma 9.14 again. The adaptive rule gives the
-- predefined formula whenever `g n = 0`, and when `g n ≠ 0` it gives
-- `t n = √(2σ) / (‖g n‖ √(n + 1))`, so in both cases one obtains the lower bound
-- `t n ≥ √(2σ) / (L_f √(n + 1))` and the estimate `(t n)^2 * ‖g n‖^2 ≤ 2σ / (n + 1)`. The same
-- harmonic-sum comparison as in part (2), together with Lemma 8.27 (1), yields the displayed
-- `O(log k / √k)` rate.
/-- Theorem 9.18 (3): under the standing constrained mirror-descent assumptions of Definitions 9.1
and 9.2, if the mirror-descent stepsizes are chosen by the adaptive rule
`t_k = √(2σ) / (‖g_k‖ √(k + 1))` when `g_k ≠ 0` and
`t_k = √(2σ) / (L_f √(k + 1))` when `g_k = 0`, then for every optimal point `xStar ∈ XStar` and
every `k ≥ 1` the running-best objective gap satisfies the same
`(L_f / √(2σ)) * (B_ω(xStar, x⁰) + 1 + log (k + 1)) / √(k + 1)` estimate. -/
theorem mirror_descent_best_value_gap_le_log_over_sqrt_of_adaptive_stepsizes
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (h_bound : SubgradientNormBoundOn f C)
    (h_traj :
      is_mirror_descent_trajectory (fun y : E ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    {k : ℕ} (hk : 1 ≤ k)
    (h_stepsize_zero :
      ∀ n, g n = 0 →
        t n = Real.sqrt (2 * σ) / (h_bound.L_f * Real.sqrt ((n : ℝ) + 1)))
    (h_stepsize_nonzero :
      ∀ n, g n ≠ 0 →
        t n = Real.sqrt (2 * σ) / (‖g n‖ * Real.sqrt ((n : ℝ) + 1))) :
    best_achieved_function_value (fun y : E ↦ (f y).toReal) x k - fOpt ≤
      (h_bound.L_f / Real.sqrt (2 * σ)) *
        (B[ω] xStar (x 0) + 1 + Real.log ((k : ℝ) + 1)) /
        Real.sqrt ((k : ℝ) + 1) := sorry

end
