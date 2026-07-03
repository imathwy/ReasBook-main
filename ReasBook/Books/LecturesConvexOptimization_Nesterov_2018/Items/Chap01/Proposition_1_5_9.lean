import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap01.Proposition_1_5_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 1.5.9 lies in the first-order smooth optimization / Taylor remainder domain.

Primary mathematical domain:
* first-order smooth optimization on a real Hilbert space

Sampled owner-style declarations:
* `HasGradientAt`
* `mem_contDiffOne_withLipschitzGradient_of_sub_affineApproximation_norm_sq_bound` in
  `LecturesConvexOptimization_Nesterov_2018.Chap01.Proposition_1_5_9`
* `LipschitzWith L g`
* `LipschitzWith.norm_sub_le`

Best owner abstraction:
* the pointwise gradient owner `HasGradientAt f (g x) x`

Primitive data:
* a function `f`
* a Lipschitz constant `L`
* a candidate gradient field `g`
* the global quadratic remainder estimate for the affine approximation
  `y ↦ f x + inner ℝ (g x) (y - x)`

Derived API:
* the `C¹` conclusion
* the identity `∇ f = g`
* the gradient-Lipschitz conclusion used in the textbook proposition

Source/core/bridge triage:
* source-facing: the textbook conclusion that the prescribed gradient field is globally
  `L`-Lipschitz
* core/canonical: the pointwise owner `HasGradientAt f (g x) x`
* bridge/view: the `C^{1,1}_L` owner theorem and its Lipschitz projection

This item now recalls the source-facing bridge theorem directly from the owner file instead of
redeclaring a parallel one-line projection. The public statement is now phrased against explicit
affine first-order data rather than the totalized gradient. -/

#check lipschitzGradient_of_sub_affineApproximation_norm_sq_bound

end
