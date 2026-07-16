import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap01.Lemma_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 1.42: the dual norm on `E*` is the canonical chapter owner declaration `dualNorm`,
defined as the operator norm of the associated continuous linear functional. -/
recall dualNorm

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: view `y` as a continuous linear functional on the finite-dimensional normed
-- space `E`, use compactness of the closed unit ball to maximize `x ↦ y x`, and replace a
-- maximizer by its negation if needed so that the maximum equals the earlier chapter definition
-- `dualNorm y`.
/-- A vector in the closed unit ball attains the dual norm, matching the textbook maximum formula
for `‖y‖_*`. -/
theorem exists_dualNorm_eq_apply (y : Module.Dual ℝ E) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ dualNorm y = y x := sorry

end
