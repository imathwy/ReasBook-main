import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E]

-- Proof sketch: use `0 ∈ interior (∂f(0))` to obtain a uniform lower bound
-- `f x ≥ ε * ‖x‖` from subgradients at `0`. Since the feasible set is closed and avoids `0`,
-- this gives a strictly positive lower bound for `f` on the feasible set. The same estimate
-- yields coercive growth, so the Chapter 3 proper-space minimizer-existence API gives a feasible
-- minimizer, whose attained objective value is therefore strictly positive.
/-- Proposition 7.1: for a conic unconstrained minimization problem, the optimal value
`min_{x ∈ Q₁} f(x)` is attained at a feasible point and that attained value is strictly positive.
-/
theorem positive_homogeneous_convex_minimizer_exists_and_pos
    (problem : ConicUnconstrainedMinimizationProblem E) :
    ∃ x ∈ problem.feasibleSet, IsMinOn problem problem.feasibleSet x ∧ 0 < problem x := sorry
