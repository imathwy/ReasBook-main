import Mathlib
import Nesterov.Chap06.Definition_6_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

universe u v

/- Proposition 6.24 lies in the Chapter 6 smoothed-primal / Danskin-gradient domain.

Sampled owner-style declarations:
- `smoothedPrimalObjective`, `smoothedPrimalObjectiveMaximand`, and
  `smoothedPrimalObjectiveArgmax` in `Chap06/Definition_6_30`, the chapter owners for the
  regularized primal smoothing formula and the canonical argmax set of the textbook maximizer
  `u_{μ₂}(x)`;
- `smoothed_maximizer_unique` in `Chap06/Proposition_6_6`, the chapter uniqueness theorem for the
  penalized dual maximizer under convexity of `\hat φ` and strong convexity of `d₂`;
- `smoothedObjective_hasFDerivAt` and `smoothedObjective_gradient_lipschitz` in
  `Chap06/Theorem_6_1`, the zero-`\hat f` whole-space smoothing surfaces;
- `explicitModelSmoothedProblem_hasFDerivWithinAt_and_gradient_lipschitzOn` in
  `Chap06/Proposition_6_10`, the additive within-set gradient/Lipschitz owner for an explicit
  model `\hat f + f_μ`.

Best owner abstraction:
- source-facing: Proposition 6.24's uniqueness, gradient formula, and Lipschitz estimate for the
  smoothed primal objective `f_{μ₂}`;
- core/canonical: `smoothedPrimalObjective`, `smoothedPrimalObjectiveArgmax`,
  `HasGradientWithinAt`, and `LipschitzOnWith`;
- bridge/view: a chosen argmax selector `uμ₂` and the Riesz-vector form
  `(InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ x))` of the textbook term `A^* u_{μ₂}(x)`.

Primitive data:
- the primal and dual feasible sets `Q₁`, `Q₂`;
- the smooth primal term `hatf`, the convex dual term `hatφ`, the prox term `d₂`, and the
  smoothing parameter `μ₂`;
- a chosen selection `uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x`;
- differentiability of `hatf` on `Q₁`, convexity of `hatφ` on `Q₂`, and `1`-strong convexity of
  `d₂` on `Q₂`.

Derived API:
- uniqueness of the feasible maximizer defining `u_{μ₂}(x)`;
- the within-set gradient formula for `smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂`;
- the corresponding Lipschitz bound on the canonical within-gradient field.

This file keeps the statement directly on the existing Chapter 6 owners instead of introducing a
parallel `u_{μ₂}` wrapper or a second smoothing owner.
-/

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

-- Proof sketch: apply the Chapter 6 uniqueness mechanism for the penalized dual maximand to each
-- fiber `x`, then use Danskin's theorem for the smoothed supremum term together with the
-- differentiability of `hatf` on `Q₁`, identifying the dual contribution with the Riesz vector of
-- `A.flip (uμ₂ x)`.
/-- Proposition 6.24 [Chapter6_2.json:64] (1): if `\hat f` is differentiable on `Q₁`, `\hat φ`
is convex on `Q₂`, `d₂` is `1`-strongly convex on `Q₂`, and `u_{μ₂}` selects a feasible maximizer
of the canonical Chapter 6 argmax owner, then that maximizer is unique for every `x ∈ Q₁` and
the smoothed primal objective has within-set gradient
`∇_Q \hat f(x) + A^* u_{μ₂}(x)`. -/
theorem smoothedPrimalObjective_argmax_unique_and_hasGradientWithinAt
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ}
    (hμ₂ : 0 < μ₂)
    (hhatφ : ConvexOn ℝ Q₂ hatφ)
    (hd₂ : StrongConvexOn Q₂ 1 d₂)
    (hhatf : DifferentiableOn ℝ hatf Q₁)
    {uμ₂ : E₁ → E₂}
    (huμ₂ : ∀ ⦃x : E₁⦄, x ∈ Q₁ →
      uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x) :
    (∀ ⦃x : E₁⦄, x ∈ Q₁ → ∀ ⦃u : E₂⦄,
      u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x → u = uμ₂ x) ∧
    ∀ ⦃x : E₁⦄, x ∈ Q₁ →
      HasGradientWithinAt
        (smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂)
        (gradientWithin hatf Q₁ x +
          (InnerProductSpace.toDual ℝ E₁).symm (A.flip (uμ₂ x)))
        Q₁ x := sorry

-- Proof sketch: combine the gradient identity from
-- `smoothedPrimalObjective_argmax_unique_and_hasGradientWithinAt` with the Chapter 6 Lipschitz
-- estimate for the smoothed supremum term, then use the additive within-gradient rule to add the
-- given Lipschitz field for `∇_Q hatf`.
/-- Proposition 6.24 [Chapter6_2.json:64] (2): if, in addition,
`x ↦ gradientWithin hatf Q₁ x` is Lipschitz on `Q₁` with constant `L₁(\hat f)`, then the
canonical within-gradient field of `f_{μ₂}` is Lipschitz on `Q₁` with constant
`L₁(\hat f) + μ₂⁻¹ ‖A‖²`. -/
theorem smoothedPrimalObjective_gradientWithin_lipschitzOn
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ} {Lhatf : NNReal}
    (hμ₂ : 0 < μ₂)
    (hhatφ : ConvexOn ℝ Q₂ hatφ)
    (hd₂ : StrongConvexOn Q₂ 1 d₂)
    (hhatf : DifferentiableOn ℝ hatf Q₁)
    {uμ₂ : E₁ → E₂}
    (huμ₂ : ∀ ⦃x : E₁⦄, x ∈ Q₁ →
      uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x)
    (hhatf_lipschitz :
      LipschitzOnWith Lhatf (fun x ↦ gradientWithin hatf Q₁ x) Q₁) :
    LipschitzOnWith
      (Lhatf + Real.toNNReal ((1 / μ₂) * ‖A‖ ^ (2 : ℕ)))
      (fun x ↦ gradientWithin (smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂) Q₁ x) Q₁ := sorry
