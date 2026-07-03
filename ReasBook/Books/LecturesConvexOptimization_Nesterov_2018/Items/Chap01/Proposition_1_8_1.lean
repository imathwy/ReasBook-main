import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap01.Proposition_1_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

universe u

/- Proposition 1.8.1 lies in the first-order smooth optimization / quadratic upper-model domain.

Relevant owner-style declarations sampled before drafting:
* `gradientMethodUpperModel_isMinOn`
* `gradientMethodUpperModel_isGlobalUpperApproximation`
* `gradientMethod`
* `quadraticallyRegularizedObjective`

Best owner abstraction:
* the canonical upper model
  `quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar`
  together with its minimizer and upper-approximation theorems already proved in
  `LecturesConvexOptimization_Nesterov_2018.Chap01.Proposition_1_8_1`

Primitive data:
* the objective `f`, base point `xBar`, and step size `h`
* the smoothness data `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)`

Derived API:
* the minimizer statement for the quadratic upper model
* the global upper-approximation inequality under `h ≤ 1 / L`

Source/core/bridge triage:
* source-facing: the textbook model `φ₁` and its minimizer / upper-bound properties
* core/canonical: the chapter owner
  `quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar`
* bridge/view: identifying the minimizer with the first constant-step gradient iterate

This item is therefore recall-only: the chapter already contains the exact canonical theorems for
both atomic clauses of the proposition, so this file reuses them directly instead of introducing
parallel wrapper declarations or a redundant local `φ₁` owner. -/

/- Proposition 1.8.1 (1): the quadratically regularized first-order Taylor model with parameter
`1 / h` is minimized at the first iterate of the constant-step gradient method, equivalently at
`xBar - h • ∇ f xBar`. -/
recall gradientMethodUpperModel_isMinOn
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (xBar : E) {h : ℝ} (hh : 0 < h) :
    IsMinOn
      (quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar)
      Set.univ
      (gradientMethod (fun _ ↦ h) f xBar 1)

/- Proposition 1.8.1 (2): if `f` has `L`-Lipschitz gradient and `0 < h` with `(L : ℝ) * h ≤ 1`,
then the same quadratic model is a global upper approximation of `f`. -/
recall gradientMethodUpperModel_isGlobalUpperApproximation
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : NNReal} (f : E → ℝ) (xBar x : E) {h : ℝ}
    (hf : ContDiff ℝ 1 f) (hgrad : LipschitzWith L (∇ f))
    (hh : 0 < h) (hLh : (L : ℝ) * h ≤ 1) :
    f x ≤
      quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar x
