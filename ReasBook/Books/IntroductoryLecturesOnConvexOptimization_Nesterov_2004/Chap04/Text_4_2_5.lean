import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_5_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.5 lies in the second-order smooth optimization domain on real Hilbert spaces.

Sampled owner-style declarations:
- `HasLipschitzContinuousHessian`
- `HasLipschitzContinuousHessian.norm_sub_le`
- `HasLipschitzContinuousHessian.gradient_deviation_le`
- `HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le`

Best owner abstraction:
- the Chapter 1 owner `HasLipschitzContinuousHessian M f`, written on theorem surfaces as
  `f ∈ C22[M]`

Primitive data:
- a function `f : E → ℝ`
- a Hessian-Lipschitz constant `M : NNReal`
- base and target points `x y : E`

Derived API:
- `HasLipschitzContinuousHessian.gradient_deviation_le`
- `HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le`

Source/core/bridge triage:
- source-facing: the gradient and second-order Taylor remainder bounds stated in Text 4.2.5
- core/canonical: the Chapter 1 owner `HasLipschitzContinuousHessian`
- bridge/view: evaluation of the owner theorems at the points `x` and `y`

Text 4.2.5 adds no new mathematics beyond the Chapter 1 owner theorems, so this file is a pure
recall item. Keeping local wrappers here would duplicate the owner API and weaken the chapter's
canonical vocabulary. -/

recall HasLipschitzContinuousHessian.gradient_deviation_le

recall HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le

end
