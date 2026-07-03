import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_7 (from Chap06) -/
/- Definition 6.7 lies in the chapter's prox-function smoothing domain.

Sampled owner-style declarations:
- `smoothedPrimalObjective` in `Definition_6_30`, the chapter's canonical owner
  of the regularized maximization formula, specialized here to zero smooth part;
- `smoothedPrimalObjectiveArgmax` in `Definition_6_30`, the chapter's
  canonical owner for the associated maximizer layer `u_μ(x)`;
- `IsProxFunction` in `Definition_6_31`, the chapter's canonical owner for the
  prox-function hypothesis on `d₂`;
- `IsProxCenter` in `Definition_6_31`, the chapter's canonical owner for the
  normalized prox-center condition.

Best owner abstraction:
- source-facing: the prox-smoothed approximation `f_μ` together with its
  associated maximizer layer `u_μ(x)`;
- core/canonical: `smoothedPrimalObjective A Q₂ 0 hatφ d₂ μ` and
  `smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ`;
- bridge/view: the prox-regularizer assumptions `IsProxFunction p Q₂ d₂` and
  `IsProxCenter Q₂ d₂ u₀`, together with the membership specification
  `u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x ↔
    u ∈ Q₂ ∧ IsMaxOn (smoothedPrimalObjectiveMaximand A hatφ d₂ μ x) Q₂ u`.

Primitive data:
- the feasible dual set `Q₂`, the dual penalty `hatφ`, the prox-function `d₂`,
  the smoothing parameter `μ`, and the linear map `A`;
- the prox-function and prox-center hypotheses, already owned by
  `IsProxFunction` and `IsProxCenter`.

Derived API:
- the smoothed objective itself, via `smoothedPrimalObjective` with zero smooth
  part;
- the canonical argmax set for the textbook point `u_μ(x)`, via
  `smoothedPrimalObjectiveArgmax`;
- its pointwise supremum formula, via `smoothedPrimalObjective_apply`;
- the pointwise maximizer specification, via
  `mem_smoothedPrimalObjectiveArgmax_iff`.

Source/core/bridge triage:
- source-facing: Definition 6.7's prox-smoothed objective `f_μ` and the
  associated maximizer layer `u_μ(x)`;
- core/canonical: `smoothedPrimalObjective`, `smoothedPrimalObjectiveArgmax`,
  `IsProxFunction`, and `IsProxCenter`;
- bridge/view: this numbered file, which only recalls those owners instead of
  packaging them into a second smoothing structure, together with the membership
  specification theorem that expands the argmax owner to feasible maximality.

The previous version introduced a parallel public owner `ProxFunctionSmoothing`
and exact wrapper API around `smoothedPrimalObjective` and `IsMaxOn`. Those notions
already have canonical owners upstream in the chapter, so this file now keeps
only the direct recall surface for the objective, its argmax owner, and the
prox hypotheses.
-/

universe u v

section

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
variable (p : Seminorm ℝ E₂) [Seminorm.IsNorm p]

variable
  (A : E₁ →L[ℝ] StrongDual ℝ E₂)
  (Q₂ : Set E₂) (hatφ d₂ : E₂ → ℝ) (μ : ℝ) (u₀ : E₂) (x : E₁) (u : E₂)

/- Definition 6.7: LecturesConvexOptimization_Nesterov_2018's prox-smoothed approximation `f_μ` is the chapter's
canonical regularized-max owner `smoothedPrimalObjective` specialized to zero
smooth part. -/
recall smoothedPrimalObjective
recall smoothedPrimalObjective_apply

/- Definition 6.7 uses the chapter's canonical prox-function owner for `d₂` and
the canonical prox-center owner for the normalized center `u₀`. -/
recall IsProxFunction
recall IsProxCenter

/- Definition 6.7's textbook maximizer `u_μ(x)` is owned by the chapter's
canonical argmax-set declaration, and membership in that set expands to the
feasible-maximizer statement. -/
recall smoothedPrimalObjectiveArgmax
recall mem_smoothedPrimalObjectiveArgmax_iff

set_option linter.hashCommand false in
#check smoothedPrimalObjective A Q₂ 0 hatφ d₂ μ x

set_option linter.hashCommand false in
#check smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x

set_option linter.hashCommand false in
#check IsProxFunction p Q₂ d₂

set_option linter.hashCommand false in
#check IsProxCenter Q₂ d₂ u₀

set_option linter.hashCommand false in
#check u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x

set_option linter.hashCommand false in
#check mem_smoothedPrimalObjectiveArgmax_iff A Q₂ hatφ d₂ μ x u

end

/-! ### Lemma_6_7 (from Chap06) -/
noncomputable section

universe u v

/- Lemma 6.7 lies in the chapter's smoothed primal objective / tangent-plane domain.

Sampled owner declarations:
- `smoothedPrimalObjectiveArgmax`, `smoothedPrimalObjectiveMaximand`, and
  `smoothedPrimalObjective` in `Chap06/Definition_6_30`, the chapter owners for the selected dual
  maximizer, the regularized dual maximand, and its supremum objective;
- `mem_smoothedPrimalObjectiveArgmax_iff` in `Chap06/Definition_6_30`, the thin bridge from the
  argmax owner to the underlying feasible-maximizer conditions;
- `ConvexOn.lower_tangent_plane_of_hasGradientWithinAt` in `Chap02/Definition_2_2`, the
  project owner for the first-order supporting inequality on a convex feasible set;
- mathlib `HasGradientWithinAt` / `gradientWithin`, the canonical within-set gradient layer.

Best owner abstraction:
- source-facing: Lemma 6.7's one-point linearization bound at a selected dual maximizer;
- core/canonical: `smoothedPrimalObjectiveArgmax`, `smoothedPrimalObjective`, `ConvexOn`, and
  `HasGradientWithinAt`;
- bridge/view: `mem_smoothedPrimalObjectiveArgmax_iff`, unpacking the argmax owner to feasibility
  and `IsMaxOn`.

Primitive data:
- `A`, `Q₁`, `Q₂`, `hatf`, `hatφ`, `d₂`, `μ₂`, `x`, `xhat`, and `u`;
- convexity of `hatf` on `Q₁`, which already packages convexity of `Q₁`;
- the source-facing argmax membership hypothesis at `xhat`;
- the within-set gradient witness for `hatf` at `xhat`;
- the sign hypotheses `0 ≤ μ₂` and `0 ≤ d₂ u`.

Derived API:
- the canonical smoothed objective value at `xhat`;
- the tangent-plane inequality for `hatf` at `xhat`;
- the bridge from argmax membership to the underlying `IsMaxOn` witness;
- the resulting affine upper bound against the selected dual value.

Source/core/bridge triage:
- source-facing: the theorem below;
- core/canonical: the owner declarations from `Definition_6_30`;
- bridge/view: the pointwise maximizer witness `u`.

The previous version rebuilt local owners `smoothedObjectiveIntegrand` and
`primalDualSmoothedObjective`. Those were exact duplicates of the chapter owners in
`Definition_6_30`, so this file now states the source-facing lemma directly against the canonical
API.
-/

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

-- Proof sketch: expand `smoothedPrimalObjective` at `xhat`, unpack the argmax membership `hu`
-- with `mem_smoothedPrimalObjectiveArgmax_iff` to bound the supremum term by the selected dual
-- value, apply the supporting-hyperplane inequality for the
-- convex function `hatf` at `xhat`, rewrite the affine pairing term as `A x u`, and drop the
-- nonpositive term `-μ₂ * d₂ u` using `μ₂ ≥ 0` and `d₂ u ≥ 0`.
/-- Lemma 6.7: if `u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ xhat`, then the affine
linearization of the smoothed primal objective at `xhat ∈ Q₁`, with the smooth contribution
written as `∇ \hat f(xhat)`, is bounded above by `\hat f(x) + ⟪A x, u⟫ - \hat φ(u)` for every
`x ∈ Q₁`. -/
theorem smoothedPrimalObjective_linearization_le_selected_dual_value
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂} {hatf : E₁ → ℝ} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ}
    (hhatf_conv : ConvexOn ℝ Q₁ hatf) (hμ₂ : 0 ≤ μ₂)
    {x xhat : E₁} (hx : x ∈ Q₁) (hxhat : xhat ∈ Q₁) {u : E₂}
    (hu : u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ xhat)
    (hhatf_grad : HasGradientWithinAt hatf (gradientWithin hatf Q₁ xhat) Q₁ xhat)
    (hd₂_nonneg : 0 ≤ d₂ u) :
    smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂ xhat +
      inner ℝ (gradientWithin hatf Q₁ xhat) (x - xhat) +
      A (x - xhat) u ≤
      hatf x + A x u - hatφ u := by
  sorry

end

/-! ### Proposition_6_7 (from Chap06) -/
noncomputable section

universe u v

/- Proposition 6.7 lies in the chapter's prox-smoothed primal-objective approximation domain.

Relevant sampled owner declarations in this domain:
- `smoothedPrimalObjectiveMaximand` in `Chap06/Definition_6_30`, the chapter owner for the
  regularized dual maximand `u ↦ ⟪A x, u⟫ - \hat φ(u) - μ d₂(u)`;
- `smoothedPrimalObjective` in `Chap06/Definition_6_30`, the chapter owner for the smoothed primal
  objective `f_μ`;
- `IsProxCenter` in `Chap06/Definition_6_31`, the canonical owner for the normalized prox-center
  data used to derive `0 ≤ D₂`;
- `Real.sSup_le`, `le_csSup`, and `csSup_le` in mathlib, the canonical supremum API for passing
  from pointwise maximand bounds to the owner-level error bound.

Best owner abstraction:
- source-facing: Proposition 6.7's approximation bound comparing the zero-smoothed objective
  `f₀ = smoothedPrimalObjective A Q₂ 0 hatφ d₂ 0` with the prox-smoothed objective
  `f_μ = smoothedPrimalObjective A Q₂ 0 hatφ d₂ μ`;
- core/canonical: `smoothedPrimalObjective` and `smoothedPrimalObjectiveMaximand`;
- bridge/view: the prox-budget hypothesis `d₂(u) ≤ D₂` on `Q₂`, together with the normalized
  prox-center witness `IsProxCenter Q₂ d₂ u₀` that forces `0 ≤ D₂`.

Primitive data:
- the linear map `A`, feasible set `Q₂`, dual term `hatφ`, prox term `d₂`, and smoothing
  parameter `μ`;
- the normalized prox-center `u₀`;
- the prox budget `D₂` as an upper bound for `d₂` on `Q₂`.

Derived API:
- the pointwise owner-level sandwich
  `f₀(x) ≥ f_μ(x) ≥ f₀(x) - μ D₂`;
- the pointwise absolute-error bound
  `|f_μ(x) - f₀(x)| ≤ μ D₂`;
- the uniform error bound on the range supremum of that absolute error.

Source/core/bridge triage:
- source-facing: `smoothedPrimalObjective_error_bounds`;
- core/canonical: `smoothedPrimalObjective`;
- bridge/view: `smoothedPrimalObjective_pointwiseErrorBound` and
  `smoothedPrimalObjective_uniformErrorBound`.

The previous revision erased the Chapter 6 smoothing owner and restated the proposition as a
generic theorem about arbitrary functions `f₀` and `fμ`. This refinement restores the proposition
to the canonical smoothing object from Definition 6.7 and derives the range-supremum error bound
from the owner-level pointwise estimate, using the prox-center normalization to discharge the
nonnegativity side condition on `μ D₂`.
-/

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

private theorem smoothedPrimalObjectiveMaximand_le_zeroSmoothed
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {Q₂ : Set E₂} {hatφ d₂ : E₂ → ℝ} {μ : ℝ} {u₀ : E₂}
    (hμ : 0 ≤ μ) (hu₀ : IsProxCenter Q₂ d₂ u₀) (x : E₁) {u : E₂} (hu : u ∈ Q₂) :
    smoothedPrimalObjectiveMaximand A hatφ d₂ μ x u ≤
      smoothedPrimalObjectiveMaximand A hatφ d₂ 0 x u := by
  rw [smoothedPrimalObjectiveMaximand, smoothedPrimalObjectiveMaximand]
  have hd₂_nonneg : 0 ≤ d₂ u := by
    have hmin := hu₀.isMinOn hu
    simpa [hu₀.value_eq_zero] using hmin
  nlinarith [mul_nonneg hμ hd₂_nonneg]

private theorem zeroSmoothedMaximand_le_smoothed_add_budget
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {Q₂ : Set E₂} {hatφ d₂ : E₂ → ℝ} {μ D₂ : ℝ}
    (hμ : 0 ≤ μ) (hD₂ : ∀ u ∈ Q₂, d₂ u ≤ D₂) (x : E₁) {u : E₂} (hu : u ∈ Q₂) :
    smoothedPrimalObjectiveMaximand A hatφ d₂ 0 x u ≤
      smoothedPrimalObjectiveMaximand A hatφ d₂ μ x u + μ * D₂ := by
  rw [smoothedPrimalObjectiveMaximand, smoothedPrimalObjectiveMaximand]
  have hmul : μ * d₂ u ≤ μ * D₂ := mul_le_mul_of_nonneg_left (hD₂ u hu) hμ
  linarith

omit [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] in
private theorem smoothedPrimalObjective_budget_nonneg
    {Q₂ : Set E₂} {d₂ : E₂ → ℝ} {μ D₂ : ℝ} {u₀ : E₂}
    (hμ : 0 ≤ μ) (hu₀ : IsProxCenter Q₂ d₂ u₀) (hD₂ : ∀ u ∈ Q₂, d₂ u ≤ D₂) :
    0 ≤ μ * D₂ := by
  have hD₂_nonneg : 0 ≤ D₂ := by
    have hbound := hD₂ u₀ hu₀.mem
    simpa [hu₀.value_eq_zero] using hbound
  exact mul_nonneg hμ hD₂_nonneg

section

variable
  {A : E₁ →L[ℝ] StrongDual ℝ E₂} {Q₂ : Set E₂} {hatφ d₂ : E₂ → ℝ}
  {μ D₂ : ℝ} {u₀ : E₂}

-- Proof sketch: compare the zero-smoothed and `μ`-smoothed maximands pointwise on `Q₂`, then pass
-- to the corresponding suprema. The prox-center normalization supplies `0 ≤ μ D₂` in the
-- unbounded-above fallback branch of the real `sSup` API.
/-- Proposition 6.7: if `μ ≥ 0`, `u₀` is a prox-center of `d₂` on `Q₂`, and `d₂(u) ≤ D₂` for
every `u ∈ Q₂`, then the Chapter 6 zero-smoothed objective
`smoothedPrimalObjective A Q₂ 0 hatφ d₂ 0` and the prox-smoothed objective
`smoothedPrimalObjective A Q₂ 0 hatφ d₂ μ` satisfy
`f₀(x) ≥ f_μ(x) ≥ f₀(x) - μ D₂` for every `x`. -/
theorem smoothedPrimalObjective_error_bounds
    (hμ : 0 ≤ μ) (hu₀ : IsProxCenter Q₂ d₂ u₀) (hD₂ : ∀ u ∈ Q₂, d₂ u ≤ D₂)
    (x : E₁) :
    smoothedPrimalObjective A Q₂ 0 hatφ d₂ 0 x ≥
      smoothedPrimalObjective A Q₂ 0 hatφ d₂ μ x ∧
    smoothedPrimalObjective A Q₂ 0 hatφ d₂ μ x ≥
      smoothedPrimalObjective A Q₂ 0 hatφ d₂ 0 x - μ * D₂ := by
  let S0 := smoothedPrimalObjectiveMaximand A hatφ d₂ 0 x '' Q₂
  let Sμ := smoothedPrimalObjectiveMaximand A hatφ d₂ μ x '' Q₂
  have hQ : Q₂.Nonempty := ⟨u₀, hu₀.mem⟩
  have hμD₂ : 0 ≤ μ * D₂ := smoothedPrimalObjective_budget_nonneg hμ hu₀ hD₂
  by_cases hS0 : BddAbove S0
  · have hSμ : BddAbove Sμ := by
      refine ⟨sSup S0, ?_⟩
      rintro y ⟨u, hu, rfl⟩
      exact
        (smoothedPrimalObjectiveMaximand_le_zeroSmoothed hμ hu₀ x hu).trans
          (le_csSup hS0 (Set.mem_image_of_mem _ hu))
    have hsSup_upper : sSup Sμ ≤ sSup S0 := by
      refine csSup_le ?_ ?_
      · simpa [Sμ] using hQ.image (smoothedPrimalObjectiveMaximand A hatφ d₂ μ x)
      · rintro y ⟨u, hu, rfl⟩
        exact
          (smoothedPrimalObjectiveMaximand_le_zeroSmoothed hμ hu₀ x hu).trans
            (le_csSup hS0 (Set.mem_image_of_mem _ hu))
    have hsSup_lower : sSup S0 ≤ sSup Sμ + μ * D₂ := by
      refine csSup_le ?_ ?_
      · simpa [S0] using hQ.image (smoothedPrimalObjectiveMaximand A hatφ d₂ 0 x)
      · rintro y ⟨u, hu, rfl⟩
        exact
          (zeroSmoothedMaximand_le_smoothed_add_budget hμ hD₂ x hu).trans
            (by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right (le_csSup hSμ (Set.mem_image_of_mem _ hu)) (μ * D₂))
    constructor
    · simpa [smoothedPrimalObjective, S0, Sμ] using hsSup_upper
    · simpa [smoothedPrimalObjective, S0, Sμ, sub_le_iff_le_add] using hsSup_lower
  · have hSμ : ¬ BddAbove Sμ := by
      intro hSμ
      apply hS0
      refine ⟨sSup Sμ + μ * D₂, ?_⟩
      rintro y ⟨u, hu, rfl⟩
      exact
        (zeroSmoothedMaximand_le_smoothed_add_budget hμ hD₂ x hu).trans
          (by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right (le_csSup hSμ (Set.mem_image_of_mem _ hu)) (μ * D₂))
    constructor
    · rw [smoothedPrimalObjective, smoothedPrimalObjective, Real.sSup_of_not_bddAbove hS0,
        Real.sSup_of_not_bddAbove hSμ]
    · rw [smoothedPrimalObjective, smoothedPrimalObjective, Real.sSup_of_not_bddAbove hS0,
        Real.sSup_of_not_bddAbove hSμ]
      linarith

/-- The owner-level error bounds of Proposition 6.7 imply the pointwise absolute approximation
estimate `|f_μ(x) - f₀(x)| ≤ μ D₂`. -/
theorem smoothedPrimalObjective_pointwiseErrorBound
    (hμ : 0 ≤ μ) (hu₀ : IsProxCenter Q₂ d₂ u₀) (hD₂ : ∀ u ∈ Q₂, d₂ u ≤ D₂)
    (x : E₁) :
    |smoothedPrimalObjective A Q₂ 0 hatφ d₂ μ x -
        smoothedPrimalObjective A Q₂ 0 hatφ d₂ 0 x| ≤
      μ * D₂ := by
  rcases smoothedPrimalObjective_error_bounds hμ hu₀ hD₂ x with ⟨hupper, hlower⟩
  refine abs_le.2 ?_
  constructor
  · linarith
  · linarith [sub_nonpos.mpr hupper]

-- Proof sketch: `IsProxCenter` and the budget hypothesis give `0 ≤ μ D₂`; then apply
-- `Real.sSup_le` to the range of the pointwise absolute error bound.
/-- The approximation estimate of Proposition 6.7 is uniform:
`sup_x |f_μ(x) - f₀(x)| ≤ μ D₂` for the canonical Chapter 6 smoothing owner. -/
theorem smoothedPrimalObjective_uniformErrorBound
    (hμ : 0 ≤ μ) (hu₀ : IsProxCenter Q₂ d₂ u₀) (hD₂ : ∀ u ∈ Q₂, d₂ u ≤ D₂) :
    sSup
        (Set.range fun x ↦
          |smoothedPrimalObjective A Q₂ 0 hatφ d₂ μ x -
              smoothedPrimalObjective A Q₂ 0 hatφ d₂ 0 x|) ≤
      μ * D₂ := by
  have hμD₂ : 0 ≤ μ * D₂ := smoothedPrimalObjective_budget_nonneg hμ hu₀ hD₂
  refine Real.sSup_le ?_ hμD₂
  rintro y ⟨x, rfl⟩
  exact smoothedPrimalObjective_pointwiseErrorBound hμ hu₀ hD₂ x

end

/-! ### Theorem_6_7 (from Chap06) -/
/- Theorem 6.7 is a recall-only item in the Chapter 6 excessive-gap / adjoint-gradient update
domain.

Primary mathematical domain:
- odd-step preservation of the `μ₁ = 0` excessive-gap condition under the strongly convex dual
  update.

Sampled owner-style declarations:
- `StronglyConvexDualUpdate.excessive_gap_condition_preserved` in `Chap06/Theorem_6_2_3`, the
  chapter owner theorem for odd-step preservation;
- `StronglyConvexDualUpdate.updatedPrimalPoint` in `Chap06/Theorem_6_2_3`, the canonical owner of
  the updated primal iterate;
- `StronglyConvexDualUpdate.updatedDualPoint` in `Chap06/Theorem_6_2_3`, the canonical owner of
  the updated dual iterate;
- `IsAdjointGradientMappingOn` in `Chap06/Definition_6_39`, the source-facing owner hypothesis for
  the dual update map.

Best owner abstraction:
- source-facing: Theorem 6.7's odd-step preservation statement;
- core/canonical: `StronglyConvexDualUpdate.excessive_gap_condition_preserved`;
- bridge/view: none. The previous local theorem duplicated the owner interface exactly, so this
  numbered item should be recall-only rather than a second public theorem shell.

Primitive data:
- the feasible sets `Q₁`, `Q₂` and their convexity;
- the smoothed primal objective `fμ`, the dual objective `φ`, and the update maps `x₀`, `uμ`,
  `V`;
- the current feasible pair `(xBar, uBar)` and the step-size data.

Derived API:
- the reduced smoothing parameter `μ₂⁺ = (1 - τ) μ₂`;
- the updated primal-dual pair from `StronglyConvexDualUpdate`;
- the preserved `μ₁ = 0` excessive-gap certificate.

This file keeps no parallel local theorem. The earlier declaration had the same binders,
hypotheses, and conclusion as the chapter owner theorem and only forwarded to it, so the correct
refinement is direct canonical recall/use. -/

/- Theorem 6.7 recalls the chapter owner theorem for odd-step preservation of the `μ₁ = 0`
excessive-gap condition. -/
recall StronglyConvexDualUpdate.excessive_gap_condition_preserved
