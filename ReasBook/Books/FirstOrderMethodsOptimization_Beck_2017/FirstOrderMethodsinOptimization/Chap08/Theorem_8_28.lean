import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Algorithm_8_3
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Assumption_8_12
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Definition_8_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)
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

/- Theorem 8.28 is `source-facing`: it gives the explicit `O(log k / √k)` convergence rate for
the concrete projected-subgradient iterates under the textbook's dynamic stepsize rule. Domain
sampling against the nearby Chapter 8 API shows that the right owner abstractions are the
projected iterate sequence `projected_subgradient_method`, the running-best value
`best_achieved_function_value`, the standing problem class `IsConstrainedConvexProblem`, and the
bound package `SubgradientNormBoundOn`. The averaged iterate `x^(k)` is a genuine textbook object,
so it is exposed directly as a concrete weighted average of the generated iterates rather than via
an existential or package wrapper. -/

/-- The stepsize-weighted average iterate
`x^(k) = (∑_{n=0}^k t_n)⁻¹ • ∑_{n=0}^k t_n x^n`
used in the ergodic projected-subgradient rate. -/
def projected_subgradient_stepsize_average_iterate
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C) (k : ℕ) : E :=
  let x :=
    projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
      h_problem.feasible_convex g t x0
  (Finset.sum (Finset.range (k + 1)) fun n ↦ t n)⁻¹ •
    Finset.sum (Finset.range (k + 1)) fun n ↦ t n • (x n : E)

-- Proof sketch: unfold `projected_subgradient_stepsize_average_iterate`; when `k = 0`, both
-- prefix sums have a single term indexed by `0`, so the weighted average is
-- `(t 0)⁻¹ • (t 0 • x^0)`. Cancel the nonzero scalar using `ht0`.
/-- If the initial stepsize is nonzero, the stepsize-weighted average iterate at `k = 0` is the
initial iterate `x^0`. -/
theorem projected_subgradient_stepsize_average_iterate_zero
    (ht0 : t 0 ≠ 0) :
    projected_subgradient_stepsize_average_iterate h_problem g t x0 0 = (x[0] : E) := sorry

-- Proof sketch: combine the weighted objective-gap estimate from Lemma 8.24 with the prefix-min
-- characterization of `best_achieved_function_value` and with Jensen's inequality for the convex
-- restriction of `f` on `C` to control the weighted average iterate. The dynamic stepsize rule
-- gives `t_n^2 ‖g_n‖^2 ≤ 1 / (n + 1)` and `t_n ≥ 1 / (L_f √(n + 1))`; substituting these bounds
-- and then applying Lemma 8.27 (1) with `D = ‖x^0 - xStar‖^2` yields the displayed
-- `O(log(k) / √k)` estimate.
/-- Theorem 8.28: under Assumptions 8.7 and 8.12, if the projected subgradient method uses the
dynamic stepsizes
`t_k = 1 / (‖f'(x^k)‖ √(k + 1))` when the chosen subgradient `f'(x^k)` is nonzero and
`t_k = 1 / L_f` otherwise, then for every `k ≥ 1` the larger of the best-value gap
`f_best^k - fOpt` and the averaged-iterate gap `f(x^(k)) - fOpt` is bounded by
`(L_f / 2) (‖x^0 - xStar‖^2 + 1 + log(k + 1)) / √(k + 1)`. -/
theorem projected_subgradient_best_and_average_value_gap_le_of_dynamic_stepsize
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_stepsize_zero :
      ∀ n, g n (x[n]) = 0 → t n = 1 / h_bound.L_f)
    (h_stepsize_nonzero :
      ∀ n,
        g n (x[n]) ≠ 0 →
          t n = 1 / (‖g n (x[n])‖ * Real.sqrt ((n : ℝ) + 1)))
    {xStar : E} (hxStar : xStar ∈ XStar) {k : ℕ} (hk : 1 ≤ k) :
    max
        (best_achieved_function_value (fun x : E ↦ (f x).toReal) (fun n ↦ (x[n] : E)) k - fOpt)
        ((f (projected_subgradient_stepsize_average_iterate h_problem g t x0 k)).toReal - fOpt) ≤
      (h_bound.L_f / 2) *
        (‖(x0 : E) - xStar‖ ^ (2 : ℕ) + 1 + Real.log ((k : ℝ) + 1)) /
          Real.sqrt ((k : ℝ) + 1) := sorry

-- Proof sketch: apply the combined max estimate from
-- `projected_subgradient_best_and_average_value_gap_le_of_dynamic_stepsize` and use
-- `le_max_left` to extract the first component.
/-- The best objective value attained by the first `k + 1` projected-subgradient iterates satisfies
the `O(log(k) / √k)` bound from the dynamic stepsize theorem. -/
theorem projected_subgradient_best_value_gap_le_of_dynamic_stepsize
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_stepsize_zero :
      ∀ n, g n (x[n]) = 0 → t n = 1 / h_bound.L_f)
    (h_stepsize_nonzero :
      ∀ n,
        g n (x[n]) ≠ 0 →
          t n = 1 / (‖g n (x[n])‖ * Real.sqrt ((n : ℝ) + 1)))
    {xStar : E} (hxStar : xStar ∈ XStar) {k : ℕ} (hk : 1 ≤ k) :
    best_achieved_function_value (fun x : E ↦ (f x).toReal) (fun n ↦ (x[n] : E)) k - fOpt ≤
      (h_bound.L_f / 2) *
        (‖(x0 : E) - xStar‖ ^ (2 : ℕ) + 1 + Real.log ((k : ℝ) + 1)) /
          Real.sqrt ((k : ℝ) + 1) := sorry

-- Proof sketch: apply the combined max estimate from
-- `projected_subgradient_best_and_average_value_gap_le_of_dynamic_stepsize` and use
-- `le_max_right` to extract the averaged-iterate component.
/-- The stepsize-weighted average iterate `x^(k)` satisfies the same `O(log(k) / √k)` objective-gap
bound as the best achieved value in the dynamic stepsize regime. -/
theorem projected_subgradient_average_value_gap_le_of_dynamic_stepsize
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_stepsize_zero :
      ∀ n, g n (x[n]) = 0 → t n = 1 / h_bound.L_f)
    (h_stepsize_nonzero :
      ∀ n,
        g n (x[n]) ≠ 0 →
          t n = 1 / (‖g n (x[n])‖ * Real.sqrt ((n : ℝ) + 1)))
    {xStar : E} (hxStar : xStar ∈ XStar) {k : ℕ} (hk : 1 ≤ k) :
    (f (projected_subgradient_stepsize_average_iterate h_problem g t x0 k)).toReal - fOpt ≤
      (h_bound.L_f / 2) *
        (‖(x0 : E) - xStar‖ ^ (2 : ℕ) + 1 + Real.log ((k : ℝ) + 1)) /
          Real.sqrt ((k : ℝ) + 1) := sorry

end
