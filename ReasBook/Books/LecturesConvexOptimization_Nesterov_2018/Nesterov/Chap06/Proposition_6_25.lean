import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Definition_1_3_3
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin Gradient

universe u v

/- Proposition 6.25 lies in the Chapter 6 smoothed-dual / Danskin-gradient domain.

Sampled owner-style declarations:
- `constrainedArgmin` with notation `argmin[Q]` in `Chap01/Definition_1_3_3`, the project owner
  for feasible minimizers of the penalized primal subproblem;
- `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the canonical bridge from an
  `EReal`-valued objective to its finite real part;
- mathlib `HasGradientWithinAt` / `gradientWithin`, the canonical within-set gradient owner;
- mathlib `LipschitzOnWith`, the canonical set-restricted Lipschitz owner.

Best owner abstraction:
- source-facing: Proposition 6.25's uniqueness, gradient, and Lipschitz statements for the
  smoothed dual objective `φ_{μ₁}`;
- core/canonical: the penalized primal minimand, the feasible argmin owner `argmin[Q₁]`, the
  `EReal`-valued smoothed dual objective below, `HasGradientWithinAt`, and `LipschitzOnWith`;
- bridge/view: the chosen minimizer section `xμ₁` and the Riesz-vector form
  `(InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u))` of the source term `A x_{μ₁}(u)`.

Source/core/bridge triage:
- source-facing: the two proposition statements below;
- core/canonical: `smoothedDualObjectiveMinimand`, `smoothedDualObjective`, and `argmin[Q₁]`;
- bridge/view: the selected minimizer map `xμ₁`.

The workspace currently lacks a usable source-level Chapter 6 owner file for `φ_{μ₁}`, so this
item is stated directly through the canonical argmin and within-gradient owners instead of through
an unavailable upstream wrapper.
-/

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/-- The penalized primal minimand
`x ↦ ⟪A x, u⟫ + \hat f(x) + μ₁ d₁(x)` whose feasible minimum defines `φ_{μ₁}(u)`. -/
def smoothedDualObjectiveMinimand
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    (hatf d₁ : E₁ → ℝ) (μ₁ : ℝ) (u : E₂) : E₁ → ℝ :=
  fun x ↦ A x u + hatf x + μ₁ * d₁ x

-- Proof sketch: unfold `smoothedDualObjectiveMinimand`.
/-- Evaluating `smoothedDualObjectiveMinimand` recovers the defining penalized primal subproblem
for the dual point `u`. -/
@[simp] theorem smoothedDualObjectiveMinimand_apply
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    (hatf d₁ : E₁ → ℝ) (μ₁ : ℝ) (u : E₂) (x : E₁) :
    smoothedDualObjectiveMinimand A hatf d₁ μ₁ u x =
      A x u + hatf x + μ₁ * d₁ x := sorry

/-- The smoothed dual objective
`φ_{μ₁}(u) = -\hat φ(u) + min_{x ∈ Q₁} {⟪A x, u⟫ + \hat f(x) + μ₁ d₁(x)}`,
recorded as an `EReal`-valued function so that its finite real part is available through
`extendedRealRealPart`. -/
def smoothedDualObjective
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (Q₁ : Set E₁)
    (hatf : E₁ → ℝ) (hatφ : E₂ → ℝ) (d₁ : E₁ → ℝ) (μ₁ : ℝ) : E₂ → EReal :=
  fun u ↦
    ((-hatφ u + sInf (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u '' Q₁)) : ℝ)

-- Proof sketch: unfold `smoothedDualObjective`.
/-- Evaluating `smoothedDualObjective` recovers `-\hat φ(u)` plus the infimum of the penalized
primal minimand over `Q₁`. -/
@[simp] theorem smoothedDualObjective_apply
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (Q₁ : Set E₁)
    (hatf : E₁ → ℝ) (hatφ : E₂ → ℝ) (d₁ : E₁ → ℝ) (μ₁ : ℝ) (u : E₂) :
    smoothedDualObjective A Q₁ hatf hatφ d₁ μ₁ u =
      ((-hatφ u + sInf (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u '' Q₁)) : ℝ) := sorry

-- Proof sketch: the affine term `x ↦ A x u` is convex on `Q₁`, `hatf` is convex by assumption,
-- and `μ₁ • d₁` is `μ₁`-strongly convex because `μ₁ > 0`; hence the whole minimand is strongly
-- convex on `Q₁`, so two feasible argmin points must coincide.
/-- The penalized primal minimand defining `x_{μ₁}(u)` has at most one feasible minimizer on
`Q₁` when `\hat f` is convex on `Q₁` and `d₁` is `1`-strongly convex on `Q₁`. -/
theorem smoothedDualObjectiveMinimand_argmin_unique
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf d₁ : E₁ → ℝ}
    {μ₁ : ℝ} (hμ₁ : 0 < μ₁)
    (hhatf : ConvexOn ℝ Q₁ hatf)
    (hd₁ : StrongConvexOn Q₁ 1 d₁)
    {u : E₂} {x y : E₁}
    (hx : x ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    (hy : y ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u)) :
    x = y := sorry

-- Proof sketch: apply the uniqueness theorem above to each fiber `u`, then use a Danskin-type
-- argument for the infimum term in `smoothedDualObjective`, combining it with the assumed
-- differentiability of `hatφ` on `Q₂`; the linear contribution is expressed via the Riesz vector
-- corresponding to the functional `A (xμ₁ u)`.
/-- Proposition 6.25 [Chapter6_2.json:67] (1): if `\hat φ` is differentiable on `Q₂`, `\hat f`
is convex on `Q₁`, `d₁` is `1`-strongly convex on `Q₁`, and `x_{μ₁}` selects a feasible minimizer
of the canonical argmin owner for each `u ∈ Q₂`, then that minimizer is unique and the finite
real part of `φ_{μ₁}` has within-set gradient `-\nabla \hat φ(u) + A x_{μ₁}(u)`, encoded by the
Riesz-vector form of `A (xμ₁ u)`. -/
theorem smoothedDualObjective_argmin_unique_and_hasGradientWithinAt
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {d₁ : E₁ → ℝ}
    {μ₁ : ℝ} (hμ₁ : 0 < μ₁)
    (hhatf : ConvexOn ℝ Q₁ hatf)
    (hd₁ : StrongConvexOn Q₁ 1 d₁)
    (hhatφ : DifferentiableOn ℝ hatφ Q₂)
    {xμ₁ : E₂ → E₁}
    (hxμ₁ : ∀ ⦃u : E₂⦄, u ∈ Q₂ →
      xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u)) :
    (∀ ⦃u : E₂⦄, u ∈ Q₂ → ∀ ⦃x : E₁⦄,
      x ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u) → x = xμ₁ u) ∧
    ∀ ⦃u : E₂⦄, u ∈ Q₂ →
      HasGradientWithinAt
        (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ d₁ μ₁))
        (-gradientWithin hatφ Q₂ u + (InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u)))
        Q₂ u := sorry

-- Proof sketch: combine the within-gradient formula above with the assumed Lipschitz control on
-- `u ↦ gradientWithin hatφ Q₂ u`, and estimate the selected-minimizer contribution by the
-- standard strong-convexity bound `μ₁⁻¹ ‖A‖²`.
/-- Proposition 6.25 [Chapter6_2.json:67] (2): if, in addition,
`u ↦ gradientWithin hatφ Q₂ u` is Lipschitz on `Q₂` with constant `L₂(\hat φ)`, then the
canonical within-gradient field of `φ_{μ₁}` is Lipschitz on `Q₂` with constant
`L₂(\hat φ) + μ₁⁻¹ ‖A‖²`. -/
theorem smoothedDualObjective_gradientWithin_lipschitzOn
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {d₁ : E₁ → ℝ}
    {μ₁ : ℝ} {Lhatφ : NNReal} (hμ₁ : 0 < μ₁)
    (hhatf : ConvexOn ℝ Q₁ hatf)
    (hd₁ : StrongConvexOn Q₁ 1 d₁)
    (hhatφ : DifferentiableOn ℝ hatφ Q₂)
    {xμ₁ : E₂ → E₁}
    (hxμ₁ : ∀ ⦃u : E₂⦄, u ∈ Q₂ →
      xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    (hhatφ_lipschitz :
      LipschitzOnWith Lhatφ (fun u ↦ gradientWithin hatφ Q₂ u) Q₂) :
    LipschitzOnWith
      (Lhatφ + Real.toNNReal ((1 / μ₁) * ‖A‖ ^ (2 : ℕ)))
      (fun u ↦
        gradientWithin
          (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ d₁ μ₁))
          Q₂ u)
      Q₂ := sorry

end
