import LecturesConvexOptimization_Nesterov_2018.Chap04.Text_4_2_6
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_2_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 4.2.4 lies in the Chapter 4 norm-power / Hessian-Lipschitz domain on real Hilbert spaces.

Sampled owner-style declarations:
* `powerDistance` in `Text_4_2_6`
* `hessian` in `Chap01/Definition_1_4_16`
* `HasLipschitzContinuousHessian` in `Definition_4_2_7`
* `HasLipschitzContinuousHessian.norm_sub_le` in `Definition_4_2_7`

Best owner abstraction:
* core/canonical: the global Hessian-Lipschitz owner
  `HasLipschitzContinuousHessian L (powerDistance p x₀)`, written on theorem surfaces as
  `powerDistance p x₀ ∈ C22[L]`

Primitive data:
* the center `x₀ : E`
* the canonical cubic power function `powerDistance (3 : ℝ) x₀`

Derived API:
* the owner membership `powerDistance (3 : ℝ) x₀ ∈ C22[2]`
* the zero-centered specialization `powerDistance (3 : ℝ) (0 : E) ∈ C22[2]`
* the pointwise Hessian estimate obtained from
  `HasLipschitzContinuousHessian.norm_sub_le`

Source/core/bridge triage:
* source-facing: the textbook Hessian estimate for `d₃(x) = (1 / 3) * ‖x‖³`
* core/canonical: the owner assertion
  `powerDistance (3 : ℝ) x₀ ∈ C22[(2 : NNReal)]`
* bridge/view: specialization to `x₀ = 0` and evaluation of the owner inequality at points `x`
  and `y`

The local definition `d3` duplicated the earlier chapter owner `powerDistance`; this file reuses
that owner directly, lifts the Hessian-Lipschitz statement to the intrinsic center parameter `x₀`,
and keeps the textbook zero-centered estimate as a thin specialization.
-/

/-- The translated cubic power function `powerDistance (3 : ℝ) x₀` has globally `2`-Lipschitz
Hessian. This is the owner-level statement underlying Lemma 4.2.4 and its translated uses. -/
theorem powerDistance_three_mem_C22 (x0 : E) :
    powerDistance (3 : ℝ) x0 ∈ C22[(2 : NNReal)] := sorry

/-- The Hessians of the translated cubic power function satisfy the owner inequality
`‖∇² d₃,x₀(x) - ∇² d₃,x₀(y)‖ ≤ 2 * ‖x - y‖`. -/
theorem powerDistance_three_hessian_norm_sub_le (x0 x y : E) :
    ‖hessian (powerDistance (3 : ℝ) x0) x -
        hessian (powerDistance (3 : ℝ) x0) y‖ ≤
      (2 : ℝ) * ‖x - y‖ := by
  simpa using
    HasLipschitzContinuousHessian.norm_sub_le (powerDistance_three_mem_C22 x0) x y

/-- Lemma 4.2.4: the centered cubic power function `d₃(x) = (1 / 3) * ‖x‖³`, realized as
`powerDistance (3 : ℝ) 0`, has globally `2`-Lipschitz Hessian. -/
theorem powerDistance_three_zero_mem_C22 :
    powerDistance (3 : ℝ) (0 : E) ∈ C22[(2 : NNReal)] := by
  simpa using powerDistance_three_mem_C22 (0 : E)

/-- Lemma 4.2.4, pointwise form: for any `x, y ∈ E`, the Hessian of the centered cubic power
function satisfies `‖∇² d₃(x) - ∇² d₃(y)‖ ≤ 2 * ‖x - y‖`. -/
theorem powerDistance_three_zero_hessian_norm_sub_le (x y : E) :
    ‖hessian (powerDistance (3 : ℝ) (0 : E)) x -
        hessian (powerDistance (3 : ℝ) (0 : E)) y‖ ≤
      (2 : ℝ) * ‖x - y‖ := by
  simpa using powerDistance_three_hessian_norm_sub_le (0 : E) x y

end
