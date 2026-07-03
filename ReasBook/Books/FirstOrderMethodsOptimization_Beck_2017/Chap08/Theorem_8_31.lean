import FirstOrderMethodsinOptimization.Chap08.Algorithm_8_3
import FirstOrderMethodsinOptimization.Chap08.Assumption_8_7
import FirstOrderMethodsinOptimization.Chap08.Assumption_8_12
import FirstOrderMethodsinOptimization.Chap08.Definition_8_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)
open scoped BigOperators

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

/- Theorem 8.31 is `source-facing`: it states the concrete `O(1 / k)` convergence guarantees for
the projected subgradient iterates in the strongly convex regime. The relevant owner abstractions
already present in the chapter are the iterate sequence `projected_subgradient_method`, the
running-best objective value `best_achieved_function_value`, the standing constrained-problem class
`IsConstrainedConvexProblem`, the norm-bound package `SubgradientNormBoundOn`, and the
canonical owner predicate `StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)` for
strong convexity. The theorem is therefore recorded directly on those owners, with no extra
wrapper for the strongly convex algorithmic regime. -/

/-- The ergodic weight `α_n^k` used in the strongly convex projected-subgradient average, with the
canonical degenerate convention `α_0^0 = 1`. For `k > 0`, this is exactly `2n / (k (k + 1))`. -/
def projected_subgradient_strongly_convex_average_weight (k n : ℕ) : ℝ :=
  if k = 0 then
    if n = 0 then 1 else 0
  else
    (2 : ℝ) * n / (k * (k + 1) : ℝ)

-- Proof sketch: unfold `projected_subgradient_strongly_convex_average_weight`; when `k = 0`, the
-- outer branch applies and the inner branch at `n = 0` gives the value `1`.
/-- The degenerate ergodic weight at `k = 0` places all mass on the initial iterate. -/
@[simp] theorem projected_subgradient_strongly_convex_average_weight_zero :
    projected_subgradient_strongly_convex_average_weight 0 0 = 1 := sorry

-- Proof sketch: unfold `projected_subgradient_strongly_convex_average_weight`; the hypothesis
-- `0 < k` rules out the degenerate branch, so the definition reduces to the displayed fraction.
/-- For `k > 0`, the strongly convex ergodic weight is the explicit coefficient
`2n / (k (k + 1))`. -/
theorem projected_subgradient_strongly_convex_average_weight_eq_of_pos
    {k n : ℕ} (hk : 0 < k) :
    projected_subgradient_strongly_convex_average_weight k n =
      (2 : ℝ) * n / (k * (k + 1) : ℝ) := sorry

/-- The weighted average iterate `x^(k)` used in the ergodic part of the strongly convex
projected-subgradient rate. -/
def projected_subgradient_strongly_convex_average_iterate
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C) (k : ℕ) : E :=
  let x :=
    projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
      h_problem.feasible_convex g t x0
  Finset.sum (Finset.range (k + 1)) fun n ↦
    projected_subgradient_strongly_convex_average_weight k n • (x n : E)

-- Proof sketch: unfold `projected_subgradient_strongly_convex_average_iterate`; for `k = 0`, the
-- range consists only of `0`, and `projected_subgradient_strongly_convex_average_weight_zero`
-- makes the unique coefficient equal to `1`.
/-- The strongly convex weighted average at `k = 0` is the initial projected iterate `x^0`. -/
theorem projected_subgradient_strongly_convex_average_iterate_zero :
    projected_subgradient_strongly_convex_average_iterate h_problem g t x0 0 = (x[0] : E) := sorry

-- Proof sketch: combine Lemma 8.11 with strong convexity to sharpen the one-step estimate by the
-- quadratic growth term `(σ / 2) ‖x[n] - xStar‖²`, then substitute the stepsize
-- `t_n = 2 / (σ (n + 1))` and use the uniform norm bound `‖g_n‖ ≤ L_f`. Multiplying by `n` and
-- summing from `0` to `k` telescopes the squared-distance terms and yields the prefix-best
-- objective gap estimate.
/-- Theorem 8.31 (1): source part (a). Under Assumptions 8.7 and 8.12, if `f` is
`σ`-strongly convex and the projected subgradient method uses the stepsizes
`t_k = 2 / (σ (k + 1))`, then the best objective value attained among the first `k + 1` iterates
satisfies the `O(1 / k)` bound
`f_best^k - fOpt ≤ 2 L_f^2 / (σ (k + 1))`. -/
theorem projected_subgradient_best_value_gap_le_of_strongly_convex_stepsize
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    best_achieved_function_value (fun x : E ↦ (f x).toReal) (fun n ↦ (x[n] : E)) k - fOpt ≤
      2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := sorry

-- Proof sketch: first apply clause (1) to the objective value of a prefix iterate attaining the
-- running minimum. Then use the quadratic growth estimate for the strongly convex constrained
-- objective `f + δ_C` at the optimal point `xStar` to convert the objective gap into the norm
-- bound `‖x[i] - xStar‖ ≤ 2 L_f / (σ √(k + 1))`.
/-- Theorem 8.31 (2): source part (a). Any iterate among the first `k + 1` steps that attains the
best objective value on that prefix lies within distance `2 L_f / (σ √(k + 1))` of the optimal
point `xStar`. -/
theorem projected_subgradient_best_iterate_dist_le_of_strongly_convex_stepsize
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) {i : ℕ} (hi : i ∈ Finset.range (k + 1))
    (hbest :
      (f (x[i] : E)).toReal =
        best_achieved_function_value (fun x : E ↦ (f x).toReal) (fun n ↦ (x[n] : E)) k) :
    ‖(x[i] : E) - xStar‖ ≤ 2 * h_bound.L_f / (σ * Real.sqrt (k + 1)) := sorry

-- Proof sketch: start from the weighted inequality obtained in the proof of clause (1), divide by
-- `k (k + 1) / 2`, and rewrite the normalized coefficients as
-- `projected_subgradient_strongly_convex_average_weight k n`. Jensen's inequality for the convex
-- restriction of `f` then yields the same `O(1 / k)` bound for the averaged iterate.
/-- Theorem 8.31 (3): source part (b). For the weighted average iterate
`x^(k) = ∑_{n=0}^k α_n^k x^n` with weights `α_n^k = 2n / (k (k + 1))` for `k > 0`, and
`x^(0) = x^0`, the objective gap also satisfies the bound
`f(x^(k)) - fOpt ≤ 2 L_f^2 / (σ (k + 1))`. -/
theorem projected_subgradient_average_value_gap_le_of_strongly_convex_stepsize
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (k : ℕ) :
    (f (projected_subgradient_strongly_convex_average_iterate h_problem g t x0 k)).toReal - fOpt ≤
      2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := sorry

-- Proof sketch: combine clause (3) with the same quadratic growth estimate used in clause (2) for
-- the strongly convex constrained objective `f + δ_C`. Rearranging the resulting inequality gives
-- the norm estimate for the averaged iterate.
/-- Theorem 8.31 (4): source part (b). The weighted average iterate `x^(k)` lies within distance
`2 L_f / (σ √(k + 1))` of the optimal point `xStar`. -/
theorem projected_subgradient_average_dist_le_of_strongly_convex_stepsize
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    ‖projected_subgradient_strongly_convex_average_iterate h_problem g t x0 k - xStar‖ ≤
      2 * h_bound.L_f / (σ * Real.sqrt (k + 1)) := sorry

end
