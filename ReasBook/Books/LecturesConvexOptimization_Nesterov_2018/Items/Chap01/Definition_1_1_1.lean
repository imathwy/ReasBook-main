import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.1.1 lies in the finite-dimensional constrained-optimization domain.

Relevant owner-style declarations sampled before refining:
* `FunctionalConstraintsMinimizationProblem` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_1_3.lean`, the
  ambient project owner for a basic feasible set, an objective, and finitely many scalar
  constraints with comparison senses;
* `GeneralMinimizationProblem` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_1_3.lean`, the textbook
  `ℝⁿ` specialization of that ambient owner;
* `FunctionalConstraintsMinimizationProblem.constraintVector` in
  `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_1_1.lean`, the canonical packaging of the scalar constraint family
  into a vector-valued map;
* `FunctionalConstraintsMinimizationProblem.mem_feasibleSet_iff` in
  `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_1_1.lean`, the owner-level feasible-set rewrite under
  inequality-only constraints.

Best owner abstraction:
* source-facing: `GeneralMinimizationProblem n m`
* core/canonical: `FunctionalConstraintsMinimizationProblem X m`
* bridge/view: `GeneralMinimizationProblem n m` as the Euclidean specialization of the ambient
  owner

Primitive data:
* `basicFeasibleSet`
* `objective`
* `constraints`
* `senses`

Derived API:
* the objective coercion
* the packaged constraint map `constraintVector`
* the inequality-only predicate `HasLeConstraints`
* the feasible-set rewrite `mem_feasibleSet_iff`

The exact source-facing owner and its supporting ambient-owner API already live in the chapter
file, so this item is refined to direct recall/use instead of introducing any parallel local
definition. -/

section

variable {n m : ℕ}

/- Definition 1.1.1: the textbook general minimization problem on `ℝⁿ` with `m` scalar
constraints is the Chapter 1 owner `GeneralMinimizationProblem n m`. -/
#check (GeneralMinimizationProblem n m)

end

section

variable {X : Type u} {m : ℕ}
variable (problem : FunctionalConstraintsMinimizationProblem X m)

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/- The ambient owner underlying `GeneralMinimizationProblem n m` is
`FunctionalConstraintsMinimizationProblem X m`. -/
#check (FunctionalConstraintsMinimizationProblem X m)

/- The objective is used through the canonical coercion to a function on the basic feasible
set. -/
recall FunctionalConstraintsMinimizationProblem.coe_apply
    (problem : FunctionalConstraintsMinimizationProblem X m)
    (x : problem.basicFeasibleSet) :
    problem x = problem.objective x

/- The scalar constraints package canonically into the vector-valued map
`problem.constraintVector`. -/
recall FunctionalConstraintsMinimizationProblem.constraintVector
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    problem.basicFeasibleSet → Λ

/- The coordinates of the packaged constraint map recover the original scalar constraint
functions. -/
recall FunctionalConstraintsMinimizationProblem.constraintVector_apply
    (problem : FunctionalConstraintsMinimizationProblem X m)
    (x : problem.basicFeasibleSet) (i : Fin m) :
    problem.constraintVector x i = problem.constraints i x

/- The inequality-only textbook case is the owner predicate `problem.HasLeConstraints`. -/
recall FunctionalConstraintsMinimizationProblem.HasLeConstraints
    (problem : FunctionalConstraintsMinimizationProblem X m) : Prop

/- Under inequality-only constraints, membership in the feasible set is exactly the coordinatewise
system `fᵢ(x) ≤ 0`. -/
recall FunctionalConstraintsMinimizationProblem.mem_feasibleSet_iff
    (problem : FunctionalConstraintsMinimizationProblem X m)
    (h : problem.HasLeConstraints) {x : problem.basicFeasibleSet} :
    x ∈ problem.feasibleSet ↔ ∀ i : Fin m, problem.constraints i x ≤ 0

end
