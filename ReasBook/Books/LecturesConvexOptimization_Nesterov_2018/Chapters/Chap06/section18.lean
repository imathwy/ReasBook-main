import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_18 (from Chap06) -/
open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 6.18 lies in the affine variational-inequality / gap-function / constrained-
minimization domain.

Sampled owner-style declarations:
- `AffineVariationalInequalityProblem` in `Definition_6_17`, the Chapter 6 owner of the primitive
  data `(Q, B)` for an affine variational inequality;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of an
  optimization problem with a feasible set and real-valued objective;
- `constrainedArgmin` / `argmin[Q]` in `Chap01/Definition_1_3_3`, the canonical owner of feasible
  minimizers on a set;
- `explicitModelSmoothedProblem` in `Definition_6_9`, the chapter pattern of keeping the
  optimization problem itself as the owner and deriving its argmin through the Chapter 1 API.

Best owner abstraction:
- source-facing: the gap function of `problem : AffineVariationalInequalityProblem E`;
- core/canonical: `AffineVariationalInequalityProblem E`, `SetConstrainedMinimizationProblem`, and
  `argmin[Q] f`;
- bridge/view: the associated gap-minimization problem on the feasible subtype.

Primitive data:
- no new primitive data beyond the owner `problem : AffineVariationalInequalityProblem E`.

Derived API:
- `problem.gapFunction : problem.feasibleSet → ℝ`;
- `problem.gapProblem : SetConstrainedMinimizationProblem problem.feasibleSet`;
- the canonical minimizer set `argmin[Set.univ] problem.gapFunction`.

Source/core/bridge triage:
- source-facing: `AffineVariationalInequalityProblem.gapFunction`;
- core/canonical: `AffineVariationalInequalityProblem E` and the Chapter 1 minimization owners;
- bridge/view: `AffineVariationalInequalityProblem.gapProblem`.

The previous file duplicated the primitive VI data by taking `(Q, B)` as separate parameters and
introduced a second public argmin wrapper. This refinement reuses the Chapter 6 owner
`AffineVariationalInequalityProblem E`, keeps the gap function as the mathematical object defined
by the source, and lets feasible minimizers be derived canonically via `argmin`.
-/

namespace AffineVariationalInequalityProblem

/-- Definition 6.18: for an affine variational inequality problem `VI(Q, B)`, the associated gap
function `ψ : Q → ℝ` sends a feasible point `w` to `max_{v ∈ Q} ⟪B(v), w - v⟫`, encoded as the
supremum over the feasible subtype `Q`. -/
def gapFunction (problem : AffineVariationalInequalityProblem E) :
    problem.feasibleSet → ℝ :=
  fun w ↦
    sSup
      (Set.range fun v : problem.feasibleSet ↦
        problem (v : E) ((w : E) - (v : E)))

/-- Expanding the gap function at a feasible point recovers the defining supremum of affine
residuals over all feasible comparison points. -/
-- Proof sketch: unfold `gapFunction`.
theorem gapFunction_def
    (problem : AffineVariationalInequalityProblem E) (w : problem.feasibleSet) :
    problem.gapFunction w =
      sSup
        (Set.range fun v : problem.feasibleSet ↦
          problem (v : E) ((w : E) - (v : E))) := sorry

/-- Evaluating the gap function gives the supremum of the affine residuals over the feasible
set. -/
@[simp] theorem gapFunction_apply
    (problem : AffineVariationalInequalityProblem E) (w : problem.feasibleSet) :
    problem.gapFunction w =
      sSup
        (Set.range fun v : problem.feasibleSet ↦
          problem (v : E) ((w : E) - (v : E))) :=
  rfl

/-- The associated optimization problem `min_{w ∈ Q} ψ(w)`, viewed canonically on the feasible
subtype. Its minimizer set is the Chapter 1 owner `argmin[Set.univ] problem.gapFunction`. -/
def gapProblem (problem : AffineVariationalInequalityProblem E) :
    SetConstrainedMinimizationProblem problem.feasibleSet where
  feasibleSet := Set.univ
  objective := problem.gapFunction

/-- The feasible set of the associated gap-minimization problem is the whole feasible subtype. -/
@[simp] theorem gapProblem_feasibleSet
    (problem : AffineVariationalInequalityProblem E) :
    problem.gapProblem.feasibleSet = Set.univ :=
  rfl

/-- Evaluating the associated gap-minimization problem recovers the gap function. -/
@[simp] theorem gapProblem_apply
    (problem : AffineVariationalInequalityProblem E) (w : problem.feasibleSet) :
    problem.gapProblem w = problem.gapFunction w :=
  rfl

end AffineVariationalInequalityProblem

end

/-! ### Proposition_6_18 (from Chap06) -/
universe u

noncomputable section

open scoped BigOperators

section

variable {X : Type u} {ι : Type*} [Fintype ι]

/-
Proposition 6.18 lies in the Chapter 6 objective-scaling / optimal-value domain.

Sampled owner-style declarations:
* `averageIndividualExpense` in `Text_6_1_4_2_Average_Individual_Expense_Bound`, the chapter's
  source-facing owner for scaling a real-valued objective by a positive factor;
* `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  whole-space owner `(.mk Set.univ f).optimalValue : EReal` for unconstrained exact optimal
  values;
* `average_individual_expense_suboptimality_bound` in
  `Text_6_1_4_2_Average_Individual_Expense_Bound`, the exact owner theorem for the scaled-gap
  estimate.

Best owner abstraction:
* source-facing: Proposition 6.18, the population-multiplicity specialization of the average
  individual expense bound;
* core/canonical: `averageIndividualExpense` together with the Chapter 1 whole-space owner
  `SetConstrainedMinimizationProblem.optimalValue`;
* bridge/view: specialization to the scale factor `P = ∑ j, (m j : ℝ)`.

Primitive data:
* the multiplicity family `m`;
* the objective `f`, iterate `xHat`, bound constant `fBar`, and index `N`.

Derived API:
* the scaling owner `averageIndividualExpense`;
* the optimal-value owner `(.mk Set.univ f).optimalValue`;
* the specialized rate bound below, whose only finite-family input is the total mass
  `∑ j, (m j : ℝ)`.

The previous file already reused the scaling owner, but it still inherited a noncanonical local
real-valued `optimalValue` from the dependency, and it fixed the multiplicity family to the
coordinate model `Fin p`. The refined file keeps only the source-facing specialization, states its
gap directly through the Chapter 1 whole-space owner in `EReal`, and exposes the multiplicities
through the canonical finite-family owner `[Fintype ι]`.
-/

-- Proof sketch: specialize `average_individual_expense_suboptimality_bound` to the scaling factor
-- `P = ∑ j, (m j : ℝ)`.
/-- Proposition 6.18: if `P = \sum_j m_j` is positive and an iterate `xHat` satisfies
`f(xHat) - f* ≤ 2 P \bar f / √(N (N + 1))`, then the scaled objective
`\bar f(x) = f(x) / P` satisfies
`\bar f(xHat) - \bar f* ≤ 2 \bar f / √(N (N + 1))`, with both optimal values taken through the
Chapter 1 whole-space owner in `EReal`. -/
theorem scaledObjective_convergence_rate_bound
    (m : ι → ℕ) (f : X → ℝ) (xHat : X) {fBar : ℝ} {N : ℕ}
    (hP : 0 < ∑ j, (m j : ℝ))
    (hbound :
      (f xHat : EReal) -
          ((.mk Set.univ f : SetConstrainedMinimizationProblem X).optimalValue) ≤
        (2 * (∑ j, (m j : ℝ)) * fBar) /
          Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) :
    (averageIndividualExpense (∑ j, (m j : ℝ)) f xHat : EReal) -
        ((.mk Set.univ (averageIndividualExpense (∑ j, (m j : ℝ)) f) :
          SetConstrainedMinimizationProblem X).optimalValue) ≤
      (2 * fBar) / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) := by
  simpa using
    average_individual_expense_suboptimality_bound (∑ j, (m j : ℝ)) f xHat hP hbound

end
