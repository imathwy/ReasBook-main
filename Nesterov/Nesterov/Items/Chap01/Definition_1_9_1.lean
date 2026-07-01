import Mathlib.Tactic.Recall
import Nesterov.Chap01.Definition_1_9_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 1.9.1 lies in the finite-dimensional quadratic-optimization domain.

Relevant owner-style declarations sampled before drafting:
* `Matrix.PosDef`, the mathlib owner packaging symmetry together with positive definiteness for
  the Hessian matrix;
* `SetConstrainedMinimizationProblem`, the chapter owner of an ambient feasible set together with
  an objective function;
* `quadraticObjective`, the chapter owner of the quadratic function
  `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪Ax, x⟫`;
* `UnconstrainedQuadraticMinimizationProblem`, the source-facing owner of the associated
  unconstrained quadratic minimization problem.

Best owner abstraction:
* source-facing: `quadraticObjective` and `UnconstrainedQuadraticMinimizationProblem n`;
* core/canonical: `Matrix.PosDef` and
  `SetConstrainedMinimizationProblem`.

Primitive data:
* `α`, `a`, `A`, and the positive-definiteness witness on `A`

Derived API:
* the displayed quadratic objective
* the stored positive-definite matrix witness `problem.posDef`
* the bridge `problem.toSetConstrainedMinimizationProblem` to the ambient Chapter 1 owner

Source/core/bridge triage:
* source-facing: the quadratic function and its associated unconstrained minimization problem;
* core/canonical: `Matrix.PosDef` and `SetConstrainedMinimizationProblem`;
* bridge/view: the ambient `SetConstrainedMinimizationProblem` over `Set.univ`.

This item is therefore best formalized as a split recall-style file. The exact source-facing owner
API already exists in the chapter file, so this item reuses it directly instead of introducing a
parallel local wrapper. -/

section

variable (α : ℝ) (a : E) (A : Mat)

/- Definition 1.9.1 (1): for `α ∈ ℝ`, `a ∈ ℝⁿ`, and a symmetric positive-definite matrix `A`,
the quadratic function is `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪Ax, x⟫`. -/
recall quadraticObjective (α : ℝ) (a : E) (A : Mat) : E → ℝ

variable (x : E)

#check
  (show
      quadraticObjective α a A x =
        α + inner ℝ a x + (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin x) x from
    rfl)

/- Definition 1.9.1 (2): the associated unconstrained quadratic minimization problem on `ℝⁿ` is
the chapter owner `UnconstrainedQuadraticMinimizationProblem n`, whose objective is the quadratic
function above and whose ambient feasible set is all of `ℝⁿ`. -/
recall UnconstrainedQuadraticMinimizationProblem (n : ℕ) : Type

variable (problem : UnconstrainedQuadraticMinimizationProblem n)

/- The positive-definite matrix-side hypothesis is stored canonically as `problem.posDef`. -/
recall UnconstrainedQuadraticMinimizationProblem.posDef
    (problem : UnconstrainedQuadraticMinimizationProblem n) : problem.A.PosDef

/- The attached objective function is canonically `quadraticObjective problem.α problem.a
problem.A`. -/
recall UnconstrainedQuadraticMinimizationProblem.objective
    (problem : UnconstrainedQuadraticMinimizationProblem n) : E → ℝ

#check
  (show
      problem.objective = quadraticObjective problem.α problem.a problem.A from
    rfl)

/- Pointwise, the attached objective has the displayed quadratic formula. -/
#check
  (show
      problem.objective x =
        problem.α + inner ℝ problem.a x +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin x) x from
    rfl)

/- The ambient Chapter 1 owner packages the problem over feasible set `Set.univ`. -/
recall UnconstrainedQuadraticMinimizationProblem.toSetConstrainedMinimizationProblem
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    SetConstrainedMinimizationProblem E

recall UnconstrainedQuadraticMinimizationProblem.toSetConstrainedMinimizationProblem_feasibleSet
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = Set.univ

end
