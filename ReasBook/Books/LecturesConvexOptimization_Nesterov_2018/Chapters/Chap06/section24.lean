import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_24 (from Chap06) -/
noncomputable section

open scoped BigOperators

universe u v

variable {ι : Type v}
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "E₂" => EuclideanSpace ℝ ι

/- Definition 6.24 lies in the Chapter 6 box-smoothing / regularized-supremum domain.

Mandatory domain-style sampling before refinement:
- `smoothedPrimalObjectiveMaximand` in `Definition_6_30`, the chapter owner of the regularized
  maximand `u ↦ ⟪A x, u⟫ - \hat φ(u) - μ d(u)`;
- `smoothedPrimalObjective` in `Definition_6_30`, the chapter owner of the corresponding supremum
  objective;
- mathlib `EuclideanSpace.proj`, the canonical coordinate linear functionals on
  `EuclideanSpace ℝ ι`;
- `Definition_6_19`, a nearby Chapter 6 specialization that keeps only the source-facing data and
  defines the final smoothing as a thin specialization of `smoothedPrimalObjective`.

Best owner abstraction:
- source-facing: the dual box `Q₂`, the weighted quadratic prox-function `d₂`, and the final
  smoothed objective attached to the row family `a` and offsets `b`;
- core/canonical: `smoothedPrimalObjective` and `smoothedPrimalObjectiveMaximand`;
- bridge/view: the row-induced linear map `A`, the affine penalty `u ↦ ∑ⱼ bⱼ uⱼ`, and the
  coordinate expansion theorems below.

Primitive data:
- the row family `a : ι → StrongDual ℝ E`;
- the offset family `b : EuclideanSpace ℝ ι`;
- the positive smoothing parameter `μ`;
- the box set `Q₂` and the weighted quadratic prox-function `d₂`.

Derived API:
- the owner-level box specialization `quadratic_box_smoothed_objective`;
- the coordinate expansion of the canonical maximand;
- the coordinate expansion of the canonical supremum formula.

Source/core/bridge triage:
- source-facing: `quadratic_box_dual_set`, `quadratic_box_prox_function`,
  `quadratic_box_smoothed_objective`;
- core/canonical: `smoothedPrimalObjective`, `smoothedPrimalObjectiveMaximand`;
- bridge/view: `quadraticBoxLinearMap`, `quadraticBoxAffinePenalty`, and the companion expansion
  theorems.

The previous revision duplicated the chapter owner by introducing a second public maximand and a
second public regularized-supremum objective specialized to the box model. This file keeps the
source-facing box set and prox term, but deletes the duplicate smoothing owners and defines the
final objective directly through `smoothedPrimalObjective`.
-/

/-- The dual box `Q₂ = {u : EuclideanSpace ℝ ι | |uⱼ| ≤ 1 for every j}` used in the quadratic
prox smoothing scheme; the textbook `ℝ^m` presentation is recovered by specializing
`ι = Fin m`. -/
def quadratic_box_dual_set : Set E₂ :=
  {u | ∀ j : ι, |u j| ≤ (1 : ℝ)}

/-- Membership in `quadratic_box_dual_set` is exactly the coordinatewise box condition
`|uⱼ| ≤ 1`. -/
@[simp] theorem mem_quadratic_box_dual_set_iff {u : E₂} :
    u ∈ quadratic_box_dual_set ↔ ∀ j : ι, |u j| ≤ (1 : ℝ) :=
  Iff.rfl

section

variable [Fintype ι]

/-- The weighted quadratic prox-function
`d₂(u) = (1 / 2) * ∑ⱼ ‖aⱼ‖ * (uⱼ)^2` attached to the row family `a`. -/
def quadratic_box_prox_function (a : ι → StrongDual ℝ E) : E₂ → ℝ :=
  fun u ↦ (1 / 2 : ℝ) * ∑ j : ι, ‖a j‖ * (u j) ^ (2 : ℕ)

/-- Evaluating `quadratic_box_prox_function a` gives the weighted half-sum
`(1 / 2) * ∑ⱼ ‖aⱼ‖ * (uⱼ)^2`. -/
@[simp] theorem quadratic_box_prox_function_apply
    (a : ι → StrongDual ℝ E) (u : E₂) :
    quadratic_box_prox_function a u =
      (1 / 2 : ℝ) * ∑ j : ι, ‖a j‖ * (u j) ^ (2 : ℕ) :=
  rfl

/-- The affine penalty `u ↦ ∑ⱼ bⱼ uⱼ` feeding the chapter owner `smoothedPrimalObjective`. -/
private def quadraticBoxAffinePenalty (b : E₂) : E₂ → ℝ :=
  fun u ↦ ∑ j : ι, b j * u j

/-- The row family `a : ι → E₁*` as the linear map `x ↦ (u ↦ ∑ⱼ aⱼ(x) uⱼ)` into the dual of
`EuclideanSpace ℝ ι`; the textbook `a₁, …, aₘ` model is recovered by specializing `ι = Fin m`. -/
private def quadraticBoxLinearMap (a : ι → StrongDual ℝ E) :
    E →L[ℝ] StrongDual ℝ E₂ :=
  ∑ j : ι, (a j).smulRight (EuclideanSpace.proj j)

@[simp] private theorem quadraticBoxLinearMap_apply
    (a : ι → StrongDual ℝ E) (x : E) (u : E₂) :
    quadraticBoxLinearMap a x u = ∑ j : ι, a j x * u j := by
  simp [quadraticBoxLinearMap, EuclideanSpace.coe_proj, mul_comm]

/-- Expanding the chapter owner maximand for the quadratic box model gives the textbook coordinate
formula `⟪Ax - b, u⟫ - μ d₂(u)`. -/
@[simp] theorem quadratic_box_smoothed_maximand_apply
    (a : ι → StrongDual ℝ E) (b : E₂) (μ : {μ : ℝ // 0 < μ}) (x : E) (u : E₂) :
    smoothedPrimalObjectiveMaximand
        (quadraticBoxLinearMap a)
        (quadraticBoxAffinePenalty b)
        (quadratic_box_prox_function a)
        (μ : ℝ) x u =
      (∑ j : ι, (a j x - b j) * u j) - (μ : ℝ) * quadratic_box_prox_function a u := by
  rw [smoothedPrimalObjectiveMaximand, quadraticBoxLinearMap_apply, quadraticBoxAffinePenalty]
  calc
    (∑ j : ι, a j x * u j) - ∑ j : ι, b j * u j - (μ : ℝ) * quadratic_box_prox_function a u
        = (∑ j : ι, (a j x * u j - b j * u j)) - (μ : ℝ) * quadratic_box_prox_function a u := by
            rw [← Finset.sum_sub_distrib]
    _ = (∑ j : ι, (a j x - b j) * u j) - (μ : ℝ) * quadratic_box_prox_function a u := by
          congr 1
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          ring

/-- Definition 6.24: for a finite row family `a : ι → E₁*`, offsets
`b : EuclideanSpace ℝ ι`, the box `Q₂ = {u : EuclideanSpace ℝ ι : |uⱼ| ≤ 1}`, and the weighted
quadratic prox-function `d₂(u) = (1 / 2) * ∑ⱼ ‖aⱼ‖ * (uⱼ)^2`, the smooth objective `f_μ` is the
Chapter 6 regularized-supremum owner specialized to this box model; the textbook presentation is
recovered by specializing `ι = Fin m`. -/
abbrev quadratic_box_smoothed_objective
    (a : ι → StrongDual ℝ E) (b : E₂) (μ : {μ : ℝ // 0 < μ}) : E → ℝ :=
  smoothedPrimalObjective
    (quadraticBoxLinearMap a)
    quadratic_box_dual_set
    0
    (quadraticBoxAffinePenalty b)
    (quadratic_box_prox_function a)
    (μ : ℝ)

/-- `quadratic_box_smoothed_objective` is exactly the Chapter 6 regularized-supremum owner
specialized to the box model data `(A, Q₂, \hat f, \hat φ, d₂)`. -/
@[simp] theorem quadratic_box_smoothed_objective_def
    (a : ι → StrongDual ℝ E) (b : E₂) (μ : {μ : ℝ // 0 < μ}) :
    quadratic_box_smoothed_objective a b μ =
      smoothedPrimalObjective
        (quadraticBoxLinearMap a)
        quadratic_box_dual_set
        0
        (quadraticBoxAffinePenalty b)
        (quadratic_box_prox_function a)
        (μ : ℝ) :=
  rfl

/-- Evaluating `quadratic_box_smoothed_objective a b μ` gives the textbook supremum of the
penalized affine maximand over the dual box `Q₂`. -/
-- Proof sketch: unfold `quadratic_box_smoothed_objective`, rewrite by
-- `smoothedPrimalObjective_apply`, and simplify the maximand with
-- `quadratic_box_smoothed_maximand_apply`.
theorem quadratic_box_smoothed_objective_spec
    (a : ι → StrongDual ℝ E) (b : E₂) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    quadratic_box_smoothed_objective a b μ x =
      sSup
        ((fun u : E₂ ↦
            (∑ j : ι, (a j x - b j) * u j) - (μ : ℝ) * quadratic_box_prox_function a u) ''
          quadratic_box_dual_set) := sorry

/-- Evaluating `quadratic_box_smoothed_objective a b μ` recovers the supremum of the penalized
affine maximand over the dual box `Q₂`. -/
@[simp] theorem quadratic_box_smoothed_objective_apply
    (a : ι → StrongDual ℝ E) (b : E₂) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    quadratic_box_smoothed_objective a b μ x =
      sSup
        ((fun u : E₂ ↦
            (∑ j : ι, (a j x - b j) * u j) - (μ : ℝ) * quadratic_box_prox_function a u) ''
          quadratic_box_dual_set) :=
  quadratic_box_smoothed_objective_spec a b μ x

end

end

/-! ### Proposition_6_24 (from Chap06) -/
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
