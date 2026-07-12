import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {X : Type u}

open scoped BigOperators

/-
Text 6.1.4.2 lies in the whole-space objective-scaling / optimal-value domain.

Mandatory domain-style sampling before refinement:
- pointwise scalar multiplication on function spaces, the canonical owner for scaling a real-valued
  objective;
- `SetConstrainedMinimizationProblem` and `SetConstrainedMinimizationProblem.optimalValue` in
  `Chap01/Definition_1_3_7`, the Chapter 1 owner for exact optimal values in `EReal`;
- `scaledObjective_convergence_rate_bound` in `Chap06/Proposition_6_18`, the direct downstream
  specialization to a finite population split.

Best owner abstraction:
- source-facing: `averageIndividualExpense`, the textbook average-cost objective;
- core/canonical: pointwise scalar multiplication on `X → ℝ` together with the whole-space owner
  `SetConstrainedMinimizationProblem.mk Set.univ`;
- bridge/view: `averageIndividualExpense P f = P⁻¹ • f`.

Primitive data:
- the population factor `P`;
- the total-expense objective `f`.

Derived API:
- the pointwise evaluation lemma below;
- the whole-space optimal values of `f` and `averageIndividualExpense P f`.

Source/core/bridge triage:
- source-facing: the average individual expense objective and its suboptimality bound;
- core/canonical: function-space scaling and `SetConstrainedMinimizationProblem.optimalValue`;
- bridge/view: the identification of the source-facing average objective with `P⁻¹ • f`.
-/

/-- The average individual expense objective `x ↦ f(x) / P` obtained by dividing the total
expense by the positive population factor `P`. -/
abbrev averageIndividualExpense (P : ℝ) (f : X → ℝ) : X → ℝ :=
  P⁻¹ • f

/-- Evaluating `averageIndividualExpense P f` at `x` gives `f(x) / P`. -/
@[simp] theorem averageIndividualExpense_apply (P : ℝ) (f : X → ℝ) (x : X) :
    averageIndividualExpense P f x = f x / P := by
  simp [averageIndividualExpense, div_eq_mul_inv, mul_comm]

-- Proof sketch: rewrite `averageIndividualExpense P f` as the canonical scalar multiple `P⁻¹ • f`,
-- compare the Chapter 1 whole-space optimal values of `f` and `averageIndividualExpense P f`, and
-- divide the assumed total-expense bound by the positive factor `P`.
/-- Text 6.1.4.2-Average Individual Expense Bound: if
`f(xHat) - f* ≤ 2 P * rBar / √(N (N + 1))` with positive population factor `P`, then the average
individual expense `\bar f(x) = f(x) / P` satisfies
`\bar f(xHat) - \bar f* ≤ 2 rBar / √(N (N + 1))`, where both optimal values are taken through the
Chapter 1 whole-space owner in `EReal`. -/
theorem average_individual_expense_suboptimality_bound
    (P : ℝ) (f : X → ℝ) (xHat : X) {rBar : ℝ} {N : ℕ}
    (hP : 0 < P)
    (hbound :
      (f xHat : EReal) - (SetConstrainedMinimizationProblem.mk Set.univ f).optimalValue ≤
        (2 * P * rBar) / Real.sqrt (N * (N + 1) : ℝ)) :
    (averageIndividualExpense P f xHat : EReal) -
        (SetConstrainedMinimizationProblem.mk Set.univ
          (averageIndividualExpense P f)).optimalValue ≤
      (2 * rBar) / Real.sqrt (N * (N + 1) : ℝ) := sorry

end
