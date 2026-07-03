import FirstOrderMethodsinOptimization.Chap08.Algorithm_8_3
import FirstOrderMethodsinOptimization.Chap08.Assumption_8_7
import FirstOrderMethodsinOptimization.Chap08.Assumption_8_12
import FirstOrderMethodsinOptimization.Chap08.Definition_8_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → EReal} {C XStar : Set E} {fOpt Θ : ℝ}
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (h_bound : SubgradientNormBoundOn f C)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k

/- Theorem 8.30 is `source-facing`: it gives the `O(1 / √k)` convergence rate for the concrete
projected-subgradient iterates when the feasible set has a known half-squared-diameter bound `Θ`
and the stepsizes are chosen by either of the two textbook rules (8.39) or (8.40). The canonical
owners already present in Chapter 8 are the iterate sequence `projected_subgradient_method`, the
running-best value `best_achieved_function_value`, the standing problem class
`IsConstrainedConvexProblem`, and the norm-bound package `SubgradientNormBoundOn`. Since the
rate depends only on the explicit diameter bound `Θ`, the redundant compactness hypothesis from
the prose is not kept in the formal statement. -/

-- Proof sketch: pick an optimal point `xStar ∈ XStar` using `h_problem.optimal_set_nonempty`.
-- Apply Lemma 8.11 and sum the one-step inequality from indices `k / 2` through `k`. The
-- half-squared-diameter bound on `C` controls the telescoping distance term because every iterate
-- and every optimal point lie in `C`. Either stepsize choice gives both
-- `t n ^ 2 * ‖g_n‖ ^ 2 ≤ 2 Θ / (n + 1)` and
-- `√(2 Θ) / (L_f √(n + 1)) ≤ t n`; combine these estimates with the running-min inequality for
-- `best_achieved_function_value` and then invoke Lemma 8.27 (2) with `D = 1` to obtain the
-- stated `O(1 / √k)` bound.
/-- Theorem 8.30: if `Θ` bounds the half squared diameter of the feasible set `C` and the
projected subgradient method uses either the textbook stepsizes
`t_k = √(2 Θ) / (L_f √(k + 1))` or
`t_k = √(2 Θ) / (‖f'(x^k)‖ √(k + 1))` with the fallback
`√(2 Θ) / (L_f √(k + 1))` when the chosen subgradient vanishes, then for every `k ≥ 2` the best
objective gap satisfies
`f_best^k - fOpt ≤ 2 (1 + log 3) L_f √(2 Θ) / √(k + 2)`. -/
theorem projected_subgradient_best_value_gap_le_of_half_squared_diameter_stepsizes
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (hΘ :
      ∀ x ∈ C, ∀ y ∈ C, (1 / 2 : ℝ) * ‖x - y‖ ^ (2 : ℕ) ≤ Θ)
    (h_stepsize :
      (∀ n,
        t n = Real.sqrt (2 * Θ) / (h_bound.L_f * Real.sqrt ((n : ℝ) + 1))) ∨
        ((∀ n,
            g n (x[n]) = 0 →
              t n = Real.sqrt (2 * Θ) / (h_bound.L_f * Real.sqrt ((n : ℝ) + 1))) ∧
          (∀ n,
            g n (x[n]) ≠ 0 →
              t n = Real.sqrt (2 * Θ) / (‖g n (x[n])‖ * Real.sqrt ((n : ℝ) + 1)))))
    {k : ℕ} (hk : 2 ≤ k) :
    best_achieved_function_value (fun x : E ↦ (f x).toReal) (fun n ↦ (x[n] : E)) k - fOpt ≤
      (2 * (1 + Real.log 3)) * h_bound.L_f * Real.sqrt (2 * Θ) /
        Real.sqrt ((k : ℝ) + 2) := sorry

end
