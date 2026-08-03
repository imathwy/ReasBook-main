import BauschkeLean.Chap26.Example_26_21

open scoped InnerProductSpace

universe u

namespace ERealFunction

section AbstractConstrainedMinimizationProblems

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Semantic recall note: `lean_leansearch` only surfaced generic variational-inequality and
-- projection owners here. The verified project-facing owner for this remark is the Chapter 26
-- bridge `mem_variationalInequalityProblem_indicator_iff` from Example 26.21.

/-- Remark 27.9: the variational inequality condition in Proposition 27.8 (vii) is exactly the
Example 26.21 variational inequality for the indicator of `C` and the constant singleton-valued
operator induced by `gradf`. -/
theorem mem_and_forall_inner_gradient_le_zero_iff_mem_variationalInequalityProblem_indicator
    {C : Set H} (hC_nonempty : C.Nonempty) {xbar gradf : H} :
    (xbar ∈ C ∧ ∀ y ∈ C, ⟪xbar - y, gradf⟫_ℝ ≤ 0) ↔
      xbar ∈ variationalInequalityProblem (ι[C]) ((fun _ : H ↦ gradf).toSetValuedOperator) := by
  have hVI :
      xbar ∈ variationalInequalityProblem (ι[C]) ((fun _ : H ↦ gradf).toSetValuedOperator) ↔
        xbar ∈ C ∧ ∀ y ∈ C, ⟪xbar - y, gradf⟫_ℝ ≤ 0 :=
    mem_variationalInequalityProblem_indicator_iff hC_nonempty
  exact hVI.symm

end AbstractConstrainedMinimizationProblems

end ERealFunction
