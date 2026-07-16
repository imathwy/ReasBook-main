import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Definition_1_4_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.4.3 lies in the unconstrained smooth minimization domain.

Relevant owner-style declarations sampled before refining:
* `SetConstrainedMinimizationProblem` in `Nesterov/Chap01/Definition_1_3_3.lean`, the chapter
  owner of a feasible set together with a real-valued objective;
* `GeneralMinimizationProblem.IsConstrained` and
  `GeneralMinimizationProblem.not_isConstrained_iff_feasibleSet_eq_univ` in
  `Nesterov/Chap01/Definition_1_1_4_1.lean`, the earlier owner of unconstrainedness;
* `GeneralMinimizationProblem.IsSmooth` in `Nesterov/Chap01/Definition_1_1_4_3.lean`, the earlier
  owner of smoothness;
* `SetConstrainedMinimizationProblem.unconstrainedSmooth_iff` in
  `Nesterov/Chap01/Definition_1_4_3.lean`, the chapter bridge back to the textbook whole-space
  differentiability formulation.

Best owner abstraction:
* source-facing: the chapter owner expression
  `¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
    problem.toGeneralMinimizationProblem.IsSmooth`;
* core/canonical: `problem.toGeneralMinimizationProblem`, together with the earlier owner
  predicates `IsConstrained` and `IsSmooth`;
* bridge/view: `SetConstrainedMinimizationProblem.unconstrainedSmooth_iff`.

Primitive data:
* `problem : SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n))`.

Derived API:
* the owner expression above;
* the bridge to `problem.feasibleSet = Set.univ ∧ Differentiable ℝ problem`;
* the consequences `feasibleSet_eq_univ_of_unconstrainedSmooth` and
  `differentiable_of_unconstrainedSmooth`.

The exact source-facing owner and companion bridge API already exist in the chapter file, so this
item is refined to a recall surface instead of keeping the unused parallel structure
`UnconstrainedSmoothMinimizationProblem`. -/

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

variable (problem : SetConstrainedMinimizationProblem E)

/- Definition 1.4.3: an unconstrained smooth minimization problem on `ℝⁿ` is the chapter owner
expression asserting that the associated general minimization problem is both unconstrained and
smooth. -/
#check (
  ¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
    problem.toGeneralMinimizationProblem.IsSmooth
)

end

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

variable {problem : SetConstrainedMinimizationProblem E}

/- The chapter owner expression is equivalent to the textbook whole-space differentiability
formulation. -/
recall SetConstrainedMinimizationProblem.unconstrainedSmooth_iff
    {problem : SetConstrainedMinimizationProblem E} :
    (¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
      problem.toGeneralMinimizationProblem.IsSmooth) ↔
      problem.feasibleSet = Set.univ ∧ Differentiable ℝ problem

/- The owner expression forces the feasible set to be all of `ℝⁿ`. -/
recall SetConstrainedMinimizationProblem.feasibleSet_eq_univ_of_unconstrainedSmooth
    {problem : SetConstrainedMinimizationProblem E}
    (h : ¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
      problem.toGeneralMinimizationProblem.IsSmooth) :
    problem.feasibleSet = Set.univ

/- The owner expression yields a differentiable objective on `ℝⁿ`. -/
recall SetConstrainedMinimizationProblem.differentiable_of_unconstrainedSmooth
    {problem : SetConstrainedMinimizationProblem E}
    (h : ¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
      problem.toGeneralMinimizationProblem.IsSmooth) :
    Differentiable ℝ problem

end
