import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Algorithm_8_3
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Assumption_8_12
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Definition_8_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → EReal} {C XStar : Set E} {fOpt σ : ℝ}
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (h_bound : SubgradientNormBoundOn f C)
variable (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k

/- Theorem 8.33 is `source-facing`: it is the explicit `ε`-complexity corollary of the strongly
convex projected-subgradient rate. The relevant owner abstractions are the projected iterate
sequence `projected_subgradient_method`, the running-best objective value
`best_achieved_function_value`, the standing problem package `IsConstrainedConvexProblem`, the
norm-bound package `SubgradientNormBoundOn`, and the strong convexity predicate
`StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)`. The averaged iterate in clause
`(2)` is kept in its explicit weighted-sum form over the projected iterates, so this item stays
on the same canonical owner layer without importing the heavier theorem file. -/

-- Proof sketch: apply Theorem 8.31 (1) to obtain
-- `f_best^k - fOpt ≤ 2 L_f^2 / (σ (k + 1))`, then use the index lower bound
-- `2 L_f^2 / (σ ε) - 1 ≤ k` to rearrange this rate estimate into
-- `2 L_f^2 / (σ (k + 1)) ≤ ε`.
/-- Theorem 8.33 (1): under the setting and assumptions of Theorem 8.31, every index `k` with
`2 L_f^2 / (σ ε) - 1 ≤ k` guarantees that the best objective value attained among the first
`k + 1` projected-subgradient iterates differs from the optimum by at most `ε`. -/
theorem projected_subgradient_best_value_gap_le_epsilon_of_strongly_convex_stepsize
    (ε : ℝ) (k : ℕ) (hε : 0 < ε)
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (hk : 2 * h_bound.L_f ^ (2 : ℕ) / (σ * ε) - 1 ≤ (k : ℝ)) :
    best_achieved_function_value (fun x : E ↦ (f x).toReal) (fun n ↦ (x[n] : E)) k - fOpt ≤ ε :=
  sorry

-- Proof sketch: apply Theorem 8.31 (3) to the weighted average iterate `x^(k)` to get
-- `f(x^(k)) - fOpt ≤ 2 L_f^2 / (σ (k + 1))`, and then use the same rearrangement of the lower
-- bound `2 L_f^2 / (σ ε) - 1 ≤ k` to conclude `f(x^(k)) - fOpt ≤ ε`.
/-- Theorem 8.33 (2): under the setting and assumptions of Theorem 8.31, the weighted average
iterate `x^(k)` also satisfies the `ε`-accuracy guarantee
`f(x^(k)) - fOpt ≤ ε` whenever `2 L_f^2 / (σ ε) - 1 ≤ k`. -/
theorem projected_subgradient_average_value_gap_le_epsilon_of_strongly_convex_stepsize
    (ε : ℝ) (k : ℕ) (hε : 0 < ε)
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (hk : 2 * h_bound.L_f ^ (2 : ℕ) / (σ * ε) - 1 ≤ (k : ℝ)) :
    (f
      (Finset.sum (Finset.range (k + 1)) fun n ↦
        (if k = 0 then
            if n = 0 then 1 else 0
          else
            (2 : ℝ) * n / (k * (k + 1) : ℝ)) •
          (x[n] : E))).toReal - fOpt ≤ ε := sorry

end
