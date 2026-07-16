import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

/- Definition 1.3.3 lies in the finite-dimensional box-constrained minimization domain.

Relevant owner-style declarations sampled before refining:
* `SetConstrainedMinimizationProblem` in `Nesterov/Chap01/Definition_1_3_3.lean`, the chapter's
  canonical owner of a feasible set together with a real-valued objective;
* `constrainedArgmin` / `argmin[Q]`, the chapter owner of constrained minimizer sets for a fixed
  feasible set `Q`;
* `zeroOneBox` in `Nesterov/Chap01/Definition_1_3_1.lean`, the chapter owner of the textbook box
  `B_n = [0,1]^n`;
* `zeroOneBoxProblem` in `Nesterov/Chap01/Definition_1_3_3.lean`, the source-facing box-problem
  specialization of the ambient owner `SetConstrainedMinimizationProblem`.

Best owner abstraction:
* source-facing owner: `zeroOneBoxProblem n f`;
* core/canonical owner: `SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n))`.

Primitive data:
* the objective `f : EuclideanSpace ℝ (Fin n) → ℝ`.

Derived API:
* the feasible-set identification `(zeroOneBoxProblem n f).feasibleSet = zeroOneBox n`;
* the constrained argmin rewrite
  `argmin[(zeroOneBoxProblem n f).feasibleSet] (zeroOneBoxProblem n f) = argmin[zeroOneBox n] f`.

Source/core/bridge triage:
* source-facing: the textbook box problem `min_{x ∈ B_n} f(x)`;
* core/canonical: `SetConstrainedMinimizationProblem` and `argmin[Q]`;
* bridge/view: `zeroOneBoxProblem_feasibleSet` and `zeroOneBoxProblem_argmin`.

The exact source-facing owner already exists in the chapter file, so this item is refined to a
recall surface instead of reintroducing a parallel local box-problem definition. -/

/- Definition 1.3.3: the textbook box-constrained problem `min_{x ∈ B_n} f(x)` is the chapter
owner `zeroOneBoxProblem n f`. -/
recall zeroOneBoxProblem (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n))

/- The feasible set of `zeroOneBoxProblem n f` is exactly the textbook box `B_n = [0,1]^n`. -/
recall zeroOneBoxProblem_feasibleSet
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (zeroOneBoxProblem n f).feasibleSet = zeroOneBox n

/- The constrained argmin set of `zeroOneBoxProblem n f` is exactly the argmin set of `f` on the
textbook box `B_n`. -/
recall zeroOneBoxProblem_argmin
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    argmin[(zeroOneBoxProblem n f).feasibleSet] (zeroOneBoxProblem n f) =
      argmin[zeroOneBox n] f
