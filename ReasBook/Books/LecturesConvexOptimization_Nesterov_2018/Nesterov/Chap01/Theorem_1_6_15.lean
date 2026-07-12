import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap01.Algorithm_1_6_1
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_5_3
import LecturesConvexOptimization_Nesterov_2018.Chap01.Theorem_1_6_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {μ L : ℝ} {M : NNRealˣ}
variable {f : E → ℝ} {xStar x0 : E}

/- Primary domain: local linear convergence of the gradient method on a real Hilbert space near a
nondegenerate critical point with Lipschitz-continuous Hessian.

Owner declarations sampled before refining:
* `HasLipschitzContinuousHessian` in `Chap04/Definition_4_2_7`, written in Chapter 1 surface
  syntax as `f ∈ C22[M]`
* `HasLipschitzContinuousHessian.gradient_deviation_le` in `Lemma_1_5_11.lean`
* `gradientMethod` in `Algorithm_1_6_1.lean`
* `HasGeometricRateOfConvergence` in `Definition_1_2_6.lean`
* `localGradientRadius` and `localGradientGap_hasGeometricRate_of_optimal_step` in
  `Theorem_1_6_14.lean`, the scalar recurrence layer behind the local rate estimate

Source/core/bridge triage:
* source-facing: the local linear-rate theorem below
* core/canonical: `HasLipschitzContinuousHessian`, `gradientMethod`, and
  `HasGeometricRateOfConvergence`
* bridge/view: the intrinsic closed ball `Q = Metric.closedBall xStar radius`, where
  `radius = localGradientRadius μ M`, together with the Hessian quadratic bounds at `xStar` and
  the scalar local recurrence for the gradient-method distance sequence

Primitive data:
* `f`, `xStar`, `x0`
* the parameters `μ`, `L`, and the Hessian-Lipschitz datum `M`
* the Chapter 1 second-order owner hypothesis `f ∈ C22[(M : NNReal)]`
* the lower/upper quadratic bounds for the owner Hessian `hessian f xStar`
* the critical-point condition `∇ f xStar = 0`

Derived API:
* the intrinsic radius owner `localGradientRadius μ M`
* the constant-step trajectory `traj`
* the geometric-rate estimate for `k ↦ ‖traj k - xStar‖`
* any needed comparison between `μ` and `L`

No parallel local first-order wrapper is introduced here. The theorem is stated directly on the
Chapter 1 Hessian-Lipschitz owner `f ∈ C22[(M : NNReal)]`; the local ball is expressed through the
radius owner `localGradientRadius μ M`, and any induced strong-convex/smooth estimates are
derived consequences rather than primitive public data. -/

local notation "radius" => localGradientRadius μ M
local notation "step" => 2 / (L + μ)
local notation "rate" => (2 * μ) / (L + 3 * μ)
local notation "traj" => gradientMethod (fun _ : ℕ ↦ step) f x0

/-- Theorem 1.6.15: if `f` has `M`-Lipschitz Hessian, the Hessian at the stationary point `xStar`
has quadratic form bounded between `μ` and `L`, and the initial point lies in the intrinsic ball
of radius `localGradientRadius μ M` around `xStar`, then the fixed-step gradient method with
step size `2 / (L + μ)` satisfies the stated geometric error bound with rate parameter
`2 * μ / (L + 3 * μ)`. -/
-- Proof sketch: apply the Chapter 1 owner estimate `hf.gradient_deviation_le` on the ball
-- centered at `xStar` to compare `∇ f x` with the linearized model
-- `hessian f xStar (x - xStar)`.
-- The Hessian bounds at `xStar` supply the source local coefficients `μ - (M / 2) r_k` and
-- `L + (M / 2) r_k` for the distance sequence `r_k = ‖x_k - xStar‖`, while `hf` keeps `M`
-- tied to the genuine Hessian-Lipschitz datum. Any comparison between `μ` and `L` needed by the
-- scalar recurrence is derived internally from these Hessian bounds rather than stored as extra
-- public data, and the initial-radius hypothesis `h0` yields `0 < μ` because `M : NNRealˣ`
-- already forces `0 < (M : ℝ)`. The scalar recurrence layer from
-- `Theorem_1_6_14` uses the optimal constant step `2 / (L + μ)` and then yields the announced
-- geometric estimate with rate parameter `2 * μ / (L + 3 * μ)`.
theorem gradient_descent_local_linear_rate
    (hf : f ∈ C22[(M : NNReal)])
    (hess_lower : ∀ z : E, μ * ‖z‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar z) z)
    (hess_upper : ∀ z : E, inner ℝ (hessian f xStar z) z ≤ L * ‖z‖ ^ (2 : ℕ))
    (hgradStar : ∇ f xStar = 0)
    (h0 : ‖x0 - xStar‖ < radius) :
    HasGeometricRateOfConvergence
      (fun k : ℕ ↦ ‖traj k - xStar‖)
      rate
      (radius * ‖x0 - xStar‖ / (radius - ‖x0 - xStar‖)) := sorry

end

end
