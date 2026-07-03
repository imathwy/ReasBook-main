import FirstOrderMethodsinOptimization.Chap08.Theorem_8_31

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → EReal} {C XStar : Set E} {fOpt : ℝ}
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k

/-- Remark 8.32: the weighted average iterates `x^(k)` from Theorem 8.31 satisfy the recursion
`x^(k+1) = (k / (k + 2)) x^(k) + (2 / (k + 2)) x^(k+1)`. -/
-- Proof sketch: unfold `projected_subgradient_strongly_convex_average_iterate` at `k + 1`, split
-- the weighted sum into the prefix through `k` and the last term `n = k + 1`, then rewrite the
-- prefix coefficients using the identity `α_n^(k+1) = (k / (k + 2)) α_n^k` and the last
-- coefficient as `α_(k+1)^(k+1) = 2 / (k + 2)`.
theorem projected_subgradient_strongly_convex_average_iterate_succ (k : ℕ) :
    projected_subgradient_strongly_convex_average_iterate h_problem g t x0 (k + 1) =
      ((k : ℝ) / (k + 2 : ℝ)) •
          projected_subgradient_strongly_convex_average_iterate h_problem g t x0 k +
        ((2 : ℝ) / (k + 2 : ℝ)) • (x[k + 1] : E) := sorry

end
