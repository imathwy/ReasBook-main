import BauschkeLean.Chap26.Definition_26_19

open scoped InnerProductSpace

universe u

namespace ERealFunction

section GeneralCharacterizationsOfMinimizers

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Semantic recall note: `lean_leansearch` only surfaced generic gradient API, not this Chapter 26
-- owner, so this file reuses the verified local surfaces `variationalInequalityProblem`,
-- `mem_variationalInequalityProblem_iff`, and `Function.toSetValuedOperator`.

/-- Remark 27.4: the gradient variational inequality from Corollary 27.3 is exactly membership
in the Definition 26.19 variational inequality problem for the singleton-valued operator induced
by the constant map `gradg`. -/
theorem gradient_inequality_iff_mem_variationalInequalityProblem_constant_gradient
    {f : H → Set.Ioi (⊥ : EReal)} {xbar gradg : H} :
    (∀ y : H,
        (⟪xbar - y, gradg⟫_ℝ : EReal) + (f xbar : EReal) ≤ (f y : EReal)) ↔
      xbar ∈ variationalInequalityProblem f
        ((fun _ : H ↦ gradg).toSetValuedOperator) := by
  rw [mem_variationalInequalityProblem_iff]
  constructor
  · rintro hineq
    exact ⟨gradg, by simp [Function.toSetValuedOperator_apply], hineq⟩
  · rintro ⟨u, hu, hineq⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hu
    simpa [hu] using hineq

end GeneralCharacterizationsOfMinimizers

end ERealFunction
