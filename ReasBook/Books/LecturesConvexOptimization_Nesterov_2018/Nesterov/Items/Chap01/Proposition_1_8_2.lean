import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap01.Proposition_1_8_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 1.8.2 lies in second-order smooth optimization / Newton quadratic models.

Relevant owner-style declarations sampled before refining:
* `secondOrderTaylorModelAt` in `Nesterov/Chap01/Definition_1_4_17`
* `hessianMatrix_toEuclideanLin` in `Nesterov/Chap01/Definition_1_4_16`
* `NewtonSystem.step` in `Nesterov/Chap01/Algorithm_1_7_1`
* `newtonSystem_step_eq_matrixFormula` and `newtonQuadraticModel_isMinOn` in
  `Nesterov/Chap01/Proposition_1_8_2`

Best owner abstraction:
* the source-facing quadratic model `secondOrderTaylorModelAt f xBar`
* the canonical Newton update `NewtonSystem.step (∇ f)` at the admissible point supplied by
  Hessian nondegeneracy

Primitive data:
* the objective `f`
* the base point `xBar`
* the positive-definite Hessian matrix `∇² f xBar`

Derived API:
* the inverse-Hessian coordinate formula for the canonical Newton step
* the minimizer statement for the quadratic Taylor model

Source/core/bridge triage:
* source-facing: the quadratic model and its minimizing Newton iterate
* core/canonical: `secondOrderTaylorModelAt` and `NewtonSystem.step`
* bridge/view: the inverse-Hessian matrix formula

This item is therefore recall-only: the chapter owner already proves the exact minimizer
statement and the source-facing matrix formula, so the local wrapper `newtonStepAt` is removed
instead of being kept as a parallel public owner. -/

/- Proposition 1.8.2 (1): if `∇² f xBar` is positive definite, then the quadratic Taylor model
`secondOrderTaylorModelAt f xBar` is minimized at the canonical Newton step. -/
recall newtonQuadraticModel_isMinOn
    (f : E → ℝ) (xBar : E) (hH : (∇² f xBar).PosDef) :
    IsMinOn
      (secondOrderTaylorModelAt f xBar)
      Set.univ
      (NewtonSystem.step (∇ f) ⟨xBar, _root_.hessian_det_ne_zero_of_posDef f xBar hH⟩)

/- Proposition 1.8.2 (2): the canonical Newton step agrees with the textbook inverse-Hessian
formula `xBar - [∇² f(xBar)]⁻¹ ∇ f(xBar)`. -/
recall _root_.newtonSystem_step_eq_matrixFormula
    (f : E → ℝ) (xBar : E) (hH : (∇² f xBar).PosDef) :
    NewtonSystem.step (∇ f) ⟨xBar, _root_.hessian_det_ne_zero_of_posDef f xBar hH⟩ =
      xBar - ((∇² f xBar)⁻¹).toEuclideanLin (∇ f xBar)
