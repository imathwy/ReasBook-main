import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_1_3
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_2_12
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_2_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient CubicRegularizationModelNotation

noncomputable section

universe u

variable {E : Type u}

/- Text 4.2.11 lies in the whole-space cubic-regularization / strong-convexity quadratic-rate
domain on real Hilbert spaces.

Sampled owner-style declarations:
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`, the chapter owner for the
  cubic model minimized by the step;
* `cubicRegularizationQuadraticApproximation_apply` in `Definition_4_1_3`, the owner expansion of
  that cubic model;
* `CubicRegularizationMapping` in `Definition_4_2_12`, the chapter owner for a chosen cubic-step
  map together with its minimizing property;
* `HasLipschitzContinuousHessian` / `f ∈ C22[L3]` in `Definition_4_2_7`, the canonical whole-space
  Hessian-Lipschitz owner;
* `StrongConvexOn.sub_le_inv_two_mul_norm_gradient_sq_of_isMinOn` in `Proposition_4_1_4`, the
  canonical Polyak-type gap bound used in the proof sketch.

Best owner abstraction:
* source-facing: the quadratic-decrease region from Text 4.2.11 and its invariance estimate;
* core/canonical: `CubicRegularizationMapping f (L3 : ℝ)`,
  `cubicRegularizationQuadraticApproximation f (L3 : ℝ) x`,
  `StrongConvexOn Set.univ σ f`, and `f ∈ C22[L3]`;
* bridge/view: the pointwise minimizing relation `step.isMinOn_apply x` for a chosen cubic-step
  owner, or a single trial point `T` satisfying the same owner relation.

Primitive data:
* the objective `f`;
* the strong-convexity modulus `σ`;
* the Hessian-Lipschitz constant `L3`;
* the global minimizer witness `IsMinOn f Set.univ xStar`;
* for the one-step gap lemmas, a cubic-model minimizing witness
  `IsMinOn (m[f; (L3 : ℝ)](x)) Set.univ T`;
* for the region invariance theorem, the chosen step owner
  `CubicRegularizationMapping f (L3 : ℝ)`.

Derived API:
* the displayed cubic model itself, reused directly from `Definition_4_1_3`;
* the whole-space `C22[L3]` smoothness owner instead of repeating `ContDiff` and a raw Hessian
  Lipschitz predicate;
* the quadratic-decrease region and its invariance theorem.

This refinement removes the duplicate local wrapper `cubicStepObjective`, rewrites the theorem
surface directly on the chapter owners `m[f; (L3 : ℝ)](x)` and `C22[L3]`, and replaces the raw
pair `(stepMap, hstep)` by the existing owner `CubicRegularizationMapping f (L3 : ℝ)`. The
quadratic-decrease region remains the source-facing declaration owned by this file. -/

section CubicRegularization

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.11 uses the existing Chapter 4 cubic-model owner and its expansion directly; this file
keeps no parallel local copy. -/
recall cubicRegularizationQuadraticApproximation
recall cubicRegularizationQuadraticApproximation_apply

end CubicRegularization

/-- The sublevel set on which the cubic-Newton gap estimate has coefficient at most `1`. It is
written in the multiplication form `2 L₃² (f x - f xStar) ≤ σ³`, which avoids division-by-zero
artifacts when `L₃ = 0`. -/
def cubicNewtonQuadraticDecreaseRegion
    (f : E → ℝ) (xStar : E) (σ : ℝ) (L3 : NNReal) : Set E :=
  {x | (2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ σ ^ (3 : ℕ)}

-- Proof sketch: unfold `cubicNewtonQuadraticDecreaseRegion`.
/-- Membership in `cubicNewtonQuadraticDecreaseRegion f xStar σ L3` is exactly the displayed
sublevel inequality `2 L₃² (f x - f xStar) ≤ σ³`. -/
theorem mem_cubicNewtonQuadraticDecreaseRegion
    {f : E → ℝ} {xStar x : E} {σ : ℝ} {L3 : NNReal} :
    x ∈ cubicNewtonQuadraticDecreaseRegion f xStar σ L3 ↔
      (2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ σ ^ (3 : ℕ) :=
  Iff.rfl

section CubicRegularization

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: combine strong convexity with the Polyak-type estimate
-- `f T - f xStar ≤ (1 / (2 * σ)) ‖∇ f T‖²`, apply Text 4.2.8 (1) with `M = L₃` to bound
-- `‖∇ f T‖` by `L₃ ‖x - T‖²`, and then use Text 4.2.8 (2) with `M = L₃` to convert
-- `‖x - T‖²` into the objective drop `f x - f T`.
/-- For a cubic-step minimizer `T`, the next optimality gap is bounded by the square of the
current one-step objective decrease. -/
theorem cubicStep_gap_le_square_of_objective_drop
    {f : E → ℝ} {σ : ℝ} {L3 : NNReal} (hσ : 0 < σ)
    (hf : f ∈ C22[L3])
    (hf_strong : StrongConvexOn Set.univ σ f)
    {xStar x T : E} (hxStar : IsMinOn f Set.univ xStar)
    (hT : IsMinOn (m[f; (L3 : ℝ)](x)) Set.univ T) :
    f T - f xStar ≤
      ((2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) / σ ^ (3 : ℕ)) * (f x - f T) ^ (2 : ℕ) := sorry

-- Proof sketch: apply `cubicStep_gap_le_square_of_objective_drop`, then use
-- `f xStar ≤ f T` from `hxStar` to get `f x - f T ≤ f x - f xStar`.
/-- For a cubic-step minimizer `T`, the next optimality gap is bounded by a quadratic function of
the current optimality gap. -/
theorem cubicStep_gap_le_square_of_current_gap
    {f : E → ℝ} {σ : ℝ} {L3 : NNReal} (hσ : 0 < σ)
    (hf : f ∈ C22[L3])
    (hf_strong : StrongConvexOn Set.univ σ f)
    {xStar x T : E} (hxStar : IsMinOn f Set.univ xStar)
    (hT : IsMinOn (m[f; (L3 : ℝ)](x)) Set.univ T) :
    f T - f xStar ≤
      ((2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) / σ ^ (3 : ℕ)) * (f x - f xStar) ^ (2 : ℕ) := sorry

-- Proof sketch: for `x` in the displayed set, the defining inequality gives
-- `((2 * L₃²) / σ³) * (f x - f xStar) ≤ 1`. Combine this with
-- `cubicStep_gap_le_square_of_current_gap` to show
-- `f (step x) - f xStar ≤ f x - f xStar`, then rewrite the latter inequality back as
-- membership in `cubicNewtonQuadraticDecreaseRegion f xStar σ L3`.
/-- Text 4.2.11: if `f ∈ C22[L3]` is `σ`-strongly convex and `step` is a cubic regularization
mapping with parameter `L₃`, then
`f (step x) - f xStar ≤ (2 L₃² / σ³) (f x - f (step x))² ≤ (2 L₃² / σ³) (f x - f xStar)²`; in
particular, the sublevel set `{x | 2 L₃² (f x - f xStar) ≤ σ³}` is invariant and is a region of
quadratic decrease for `step`. -/
theorem cubicNewton_quadraticDecreaseRegion
    {f : E → ℝ} {σ : ℝ} {L3 : NNReal} (hσ : 0 < σ)
    (hf : f ∈ C22[L3])
    (hf_strong : StrongConvexOn Set.univ σ f)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (step : CubicRegularizationMapping f (L3 : ℝ))
    {x : E} (hx : x ∈ cubicNewtonQuadraticDecreaseRegion f xStar σ L3) :
    step x ∈ cubicNewtonQuadraticDecreaseRegion f xStar σ L3 ∧
      f (step x) - f xStar ≤
        ((2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) / σ ^ (3 : ℕ)) * (f x - f xStar) ^ (2 : ℕ) := sorry

end CubicRegularization
