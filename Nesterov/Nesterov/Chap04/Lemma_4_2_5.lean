import Nesterov.Chap01.Lemma_1_5_11
import Nesterov.Chap04.Lemma_4_1_4
import Nesterov.Chap04.Definition_4_2_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open scoped ConstrainedArgmin
open scoped CubicRegularizationModelNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 4.2.5 lies in the cubic-regularization / Hessian-Lipschitz remainder domain on complete
real inner-product spaces.

Sampled owner declarations:
* `HasLipschitzContinuousHessian` in `Definition_4_2_7`
* `HasLipschitzContinuousHessian.gradient_deviation_le` in `Chap01/Lemma_1_5_11`
* `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation` in `Lemma_4_1_4`
* `hessian` in `Chap01/Definition_1_4_16`
* `cubicRegularization_firstOrderOptimalityCondition_of_mem_argmin` in `Definition_4_2_12`
* `argmin[Set.univ] (m[f; M](x))` in `Definition_4_1_3`

Best owner abstraction:
* the global Hessian-Lipschitz owner `f ∈ C22[L3]`
* the canonical cubic-step owner
  `argmin[Set.univ] (m[f; M](x))`

Primitive data:
* the owner hypothesis `hf : f ∈ C22[L3]`
* the cubic-step membership
  `T ∈ argmin[Set.univ] (m[f; M](x))`

Derived API:
* the gradient remainder bound
  `HasLipschitzContinuousHessian.gradient_deviation_le hf x T`
* the owner radius estimate derived from
  `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation`
* the cubic-step first-order optimality equation
  `cubicRegularization_firstOrderOptimalityCondition_of_mem_argmin`

Source/core/bridge triage:
* source-facing: the gradient-pairing lower bound for one cubic-regularized Newton step
* core/canonical: `f ∈ C22[L3]` and `hessian f x`
* bridge/view: the first-order optimality equation extracted from the cubic-step owner

The previous theorem used a free linear operator `B : E →ₗ[ℝ] E` with pointwise axioms forcing the
cubic term back to the standard Euclidean-radius expression. In this plain real inner-product-space
setting, that extra wrapper is not the mathematical owner. This refinement keeps the source-facing
pairing estimate, but moves the step hypothesis to the canonical cubic-step owner
`argmin[Set.univ] (m[f; M](x))` and uses the intrinsic radius
`‖T - x‖` together with the owner first-order optimality equation. -/

-- Proof sketch: first derive the radius lower bound
-- `‖T - x‖² ≥ (2 / (L₃ + M)) * ‖∇ f T‖` internally from
-- `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation`, using
-- `hM : 2 * L₃ ≤ M` to get `0 ≤ M`. Then apply the owner theorem
-- `HasLipschitzContinuousHessian.gradient_deviation_le hf x T`, combine it with
-- `cubicRegularization_firstOrderOptimalityCondition_of_mem_argmin (hf.contDiff.contDiffAt x) hT`,
-- and obtain
-- `‖∇ f T + ((1 / 2) * M * ‖T - x‖) • (T - x)‖² ≤ ((L₃ / 2) * ‖T - x‖²)²`. Expanding the square
-- yields a lower bound for `⟪∇ f T, x - T⟫` in terms of
-- `‖∇ f T‖² / (M * ‖T - x‖)` and `((M² - L₃²) / (4 * M)) * ‖T - x‖³`. The assumption
-- `2 * L₃ ≤ M` makes this lower bound monotone on the feasible ray
-- `‖T - x‖² ≥ 2 ‖∇ f T‖ / (L₃ + M)`. Since `L₃ : NNReal` and `hM` force
-- `0 ≤ (L₃ : ℝ) + M`, the square-root coefficient is well-defined internally; in the degenerate
-- case `L₃ = M = 0`, the right-hand side vanishes. Evaluating the lower bound at the boundary
-- gives the stated
-- `‖∇ f T‖^(3 / 2)` estimate.
/-- Lemma 4.2.5: if `f ∈ C22[L₃]`, if `T` belongs to the canonical cubic-regularization step set
`argmin[Set.univ] (m[f; M](x))`, and if `2 L₃ ≤ M`, then
`⟪∇ f(T), x - T⟫ ≥ √(2 / (L₃ + M)) ‖∇ f(T)‖^(3 / 2)`. -/
theorem cubicRegularization_gradientPairing_ge_sqrt_mul_gradientNorm_rpow_threeHalves
    {f : E → ℝ} {L3 : NNReal} (hf : f ∈ C22[L3]) {x T : E} {M : ℝ}
    (hM : 2 * (L3 : ℝ) ≤ M)
    (hT : T ∈ argmin[Set.univ] (m[f; M](x))) :
    inner ℝ (∇ f T) (x - T) ≥
      Real.sqrt (2 / ((L3 : ℝ) + M)) * Real.rpow ‖∇ f T‖ (3 / 2 : ℝ) := sorry
