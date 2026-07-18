import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Lemma_8_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)
noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (f : E → EReal) (C XStar : Set E) (fOpt : ℝ)
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k

-- Proof sketch: apply `projected_subgradient_method_fundamental_inequality` for each
-- `n ∈ Finset.range (k + 1)`, sum the resulting inequalities, and use telescoping on the squared
-- distance terms. Then drop the nonnegative final term `‖x[k + 1] - xStar‖^2 / 2`.
/-- Lemma 8.24: under Assumption 8.7, the stepsize-weighted cumulative objective gap along the
projected subgradient iterates up to step `k` is bounded by one half of the initial squared
distance to an optimal point plus one half of the accumulated squared subgradient norms. -/
theorem projected_subgradient_method_weighted_objective_gap_sum_le
    (h_subgrad :
      ∀ k,
        (toDualMap ℝ E (g k (x[k])) : Module.Dual ℝ E) ∈ extendedRealSubdifferential f (x[k] : E))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * ((f (x[n] : E)).toReal - fOpt)) ≤
      (1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ 2 +
        (1 / 2 : ℝ) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ 2 * ‖g n (x[n])‖ ^ 2) := sorry

end
