import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: use the interior assumption to choose a closed ball contained in
-- `effective_domain f`. The hypothesis `h_ne_bot` supplies the exact codomain restriction needed
-- for the chapter bridge `convexOn_toReal_of_is_convex_function`, so that `x ↦ (f x).toReal` is a
-- genuine real-valued convex function on `effective_domain f`. Apply the finite-dimensional theorem
-- that convex functions are locally Lipschitz on the interior of their domain, then shrink to a
-- closed ball and rewrite the resulting Lipschitz estimate as the displayed bound at `x0`.
/-- Theorem 2.9: a convex extended-real-valued function is locally Lipschitz at every point of the
interior of its effective domain, in the sense that some closed ball around the point is contained
in the domain and satisfies the estimate `|(f x).toReal - (f x0).toReal| ≤ L * ‖x - x0‖`. -/
theorem convex_function_exists_closedBall_lipschitz_bound_at_interior_point
    {f : E → EReal} (hf : is_convex_function f)
    (h_ne_bot : ∀ x, f x ≠ ⊥) {x0 : E} (hx0 : x0 ∈ interior (effective_domain f)) :
    ∃ ε > 0, ∃ L > 0,
      Metric.closedBall x0 ε ⊆ effective_domain f ∧
        ∀ x ∈ Metric.closedBall x0 ε,
          |(f x).toReal - (f x0).toReal| ≤ L * ‖x - x0‖ := sorry

end
