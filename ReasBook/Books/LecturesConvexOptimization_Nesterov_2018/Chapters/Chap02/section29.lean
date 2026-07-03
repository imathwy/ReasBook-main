import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_29 (from Chap02) -/
local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "e₁" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

/-
Primary domain: elementary Euclidean convex geometry in `ℝ²`, centered around the textbook disk
`Q₁`.

Relevant owner-style declarations sampled before refining:
* `Metric.closedBall`, the canonical owner for closed Euclidean balls;
* `Metric.mem_closedBall`, the owner membership criterion for `closedBall`;
* `dist_eq_norm`, the canonical bridge from metric distance to the Euclidean norm;
* `convex_closedBall`, the standard derived convexity API used downstream.

Best owner abstraction:
* `Q₁ : Set (EuclideanSpace ℝ (Fin 2))`, as the source-facing disk itself.

Primitive data:
* the center `e₁ = (1, 0)`;
* radius `1`.

Derived API:
* the norm-form membership criterion `mem_Q₁_iff`.

Source/core/bridge triage:
* source-facing: the textbook disk `Q₁`;
* core/canonical: `Metric.closedBall e₁ 1`;
* bridge/view: `mem_Q₁_iff`.

This file therefore keeps the source-facing owner `Q₁` and reuses the canonical closed-ball API
directly, without a redundant self-equality wrapper around the definition.
-/

/-- Definition 2.29: `Q₁` is the closed Euclidean unit disk in `ℝ²` centered at `e₁ = (1, 0)`.
-/
def Q₁ : Set E :=
  Metric.closedBall e₁ (1 : ℝ)

/-- Membership in `Q₁` is equivalent to the textbook norm inequality `‖x - e₁‖ ≤ 1`. -/
-- Proof sketch: unfold `Q₁`, rewrite membership in the closed ball using
-- `Metric.mem_closedBall`, and then identify the metric distance with the Euclidean norm via
-- `dist_eq_norm`.
theorem mem_Q₁_iff (x : E) :
    x ∈ Q₁ ↔ ‖x - e₁‖ ≤ (1 : ℝ) := by
  simp [Q₁, Metric.mem_closedBall, dist_eq_norm]

attribute [simp] mem_Q₁_iff

/-! ### Proposition_2_29 (from Chap02) -/
noncomputable section

/-
Primary domain: scalar geometric-decay thresholds for the residual sequence `n ↦ tStar - t n`.

Owner-style declarations sampled before refining:
* `HasGeometricRateOfConvergence` in `Chap01/Definition_1_2_6.lean`
* `HasGeometricRateOfConvergence.of_step_bound` in `Chap01/Definition_1_2_6.lean`
* `HasGeometricRateOfConvergence.le_target_of_iterationThreshold_le` and
  `HasGeometricRateOfConvergence.iterationThreshold` in `Chap01/Definition_1_2_6.lean`
* `constrainedMinimizationInternalGap_hasGeometricRateOfConvergence` in
  `Chap02/Proposition_2_30.lean`

Best owner abstraction:
* `HasGeometricRateOfConvergence` for the residual sequence `n ↦ tStar - t n`

Primitive data:
* the scalar sequence `t`
* the limit value `tStar`
* the one-step contraction inequality on the residuals

Derived API:
* the owner geometric-rate statement for `n ↦ tStar - t n`
* the owner exact logarithmic-threshold consequences
* the source-facing specialization to Proposition 2.29

Source/core/bridge triage:
* source-facing: Proposition 2.29 and its nat-ceil corollary
* core/canonical: `HasGeometricRateOfConvergence`
* bridge/view: the recurrence-to-owner theorem
  `residual_hasGeometricRateOfConvergence`

The recurrence-to-owner bridge stays local. The public proposition specializes the canonical owner
theorem `HasGeometricRateOfConvergence.le_target_of_iterationThreshold_le` to the residual
sequence and the exact base-`2 * (1 - κ)` threshold from the text.
-/

open HasGeometricRateOfConvergence

section

variable {κ tStar : ℝ} {t : ℕ → ℝ}

local notation "base" => 2 * (1 - κ)
local notation "residual" => fun n : ℕ ↦ tStar - t n

/-- Helper for Proposition 2.29: the one-step residual contraction is exactly the owner
geometric-rate statement for the residual sequence. -/
theorem residual_hasGeometricRateOfConvergence
    (hκ_contract : 1 < 2 * (1 - κ))
    (hstep : ∀ n : ℕ, residual (n + 1) ≤ residual n / (2 * (1 - κ))) :
    HasGeometricRateOfConvergence residual (1 - (2 * (1 - κ))⁻¹) (residual 0) := by
  -- The contraction hypothesis gives the nonnegativity needed to place the owner parameter in
  -- the admissible interval `(-∞, 1]`.
  have hfactor_nonneg : 0 ≤ (2 * (1 - κ))⁻¹ := by
    have hfactor_pos : 0 < 2 * (1 - κ) := lt_trans zero_lt_one hκ_contract
    exact inv_nonneg.mpr hfactor_pos.le
  have hq₁ : 1 - (2 * (1 - κ))⁻¹ ≤ 1 := by
    simpa using sub_le_self (1 : ℝ) hfactor_nonneg
  -- Rewrite the textbook division step as the owner multiplicative step `(1 - q) * residual n`.
  refine of_step_bound hq₁ le_rfl ?_
  intro n
  calc
    residual (n + 1) ≤ residual n / (2 * (1 - κ)) := hstep n
    _ = residual n * (2 * (1 - κ))⁻¹ := by rw [div_eq_mul_inv]
    _ = (1 - (1 - (2 * (1 - κ))⁻¹)) * residual n := by ring

/-- Helper for Proposition 2.29: the textbook contraction base `2 * (1 - κ)` is the reciprocal
owner base `(1 - q)⁻¹` attached to `q = 1 - (2 * (1 - κ))⁻¹`. -/
private theorem owner_contract
    (hκ_contract : 1 < 2 * (1 - κ)) :
    1 < (1 - (1 - base⁻¹))⁻¹ := by
  have hbase_pos : 0 < base := lt_trans zero_lt_one hκ_contract
  have hbase_ne : base ≠ 0 := ne_of_gt hbase_pos
  simpa [hbase_ne] using hκ_contract

/-- Helper for Proposition 2.29: the owner iteration threshold simplifies to the textbook
logarithmic expression `N(ε)`. -/
private theorem residual_iterationThreshold_eq_textbook
    {ε : ℝ} :
    iterationThreshold (1 - (2 * (1 - κ))⁻¹) (tStar - t 0) ((1 - κ) * ε) =
      Real.log ((tStar - t 0) / ((1 - κ) * ε)) / Real.log (2 * (1 - κ)) := by
  -- Expand the owner threshold and normalize the logarithm base.
  rw [iterationThreshold, Real.logb]
  simp

/-- Proposition 2.29: if the residual sequence satisfies
`t^* - t_{n + 1} ≤ (t^* - t_n) / (2 (1 - κ))` at every step and `1 < 2 * (1 - κ)`, then every
iterate index `n ≥ N(ε)` satisfies `t^* - t_n ≤ (1 - κ) ε`, where `N(ε)` is the explicit
logarithmic threshold from the proposition. -/
-- Proof sketch: the recurrence defines an owner geometric-rate bound on the residual sequence
-- `n ↦ tStar - t n`; evaluating that bound at the iterate `n` gives
-- `tStar - t n ≤ (tStar - t 0) * ((2 * (1 - κ))⁻¹)^n`. Solve the resulting scalar inequality
-- by taking logarithms under the contraction hypothesis `1 < 2 * (1 - κ)`. The textbook side
-- assumptions `0 < κ < 1` and the residual-positivity guards are redundant for this scalar
-- consequence, so the public Lean theorem keeps only the sharper contraction hypothesis together
-- with the actual one-step contraction inequality.
theorem constrainedMinimization_error_le_target_of_iterationThreshold_le
    {ε : ℝ} (hκ_contract : 1 < 2 * (1 - κ)) (hε : 0 < ε)
    (hstep :
      ∀ n : ℕ, tStar - t (n + 1) ≤ (tStar - t n) / (2 * (1 - κ)))
    {n : ℕ}
    (hn :
      Real.log ((tStar - t 0) / ((1 - κ) * ε)) / Real.log (2 * (1 - κ)) ≤ (n : ℝ)) :
    tStar - t n ≤ (1 - κ) * ε := by
  have hresidual := residual_hasGeometricRateOfConvergence hκ_contract hstep
  have htarget_pos : 0 < (1 - κ) * ε := by
    have hone_sub_kappa_pos : 0 < 1 - κ := by
      nlinarith
    positivity
  have howner_threshold :
      iterationThreshold (1 - (2 * (1 - κ))⁻¹) (residual 0) ((1 - κ) * ε) ≤ (n : ℝ) := by
    change iterationThreshold (1 - (2 * (1 - κ))⁻¹) (tStar - t 0) ((1 - κ) * ε) ≤ (n : ℝ)
    rw [residual_iterationThreshold_eq_textbook]
    exact hn
  change residual n ≤ (1 - κ) * ε
  exact
    le_target_of_iterationThreshold_le hresidual (owner_contract hκ_contract) htarget_pos
      howner_threshold

/-- The ceiling of the logarithmic threshold gives an upper bound on the number of full
iterations required to reach the target error level `(1 - κ) ε`. -/
-- Proof sketch: apply
-- `constrainedMinimization_error_le_target_of_iterationThreshold_le` at the iterate index
-- `⌈log ((t^* - t_0) / ((1 - κ) ε)) / log (2 * (1 - κ))⌉₊`, or equivalently the owner threshold
-- `⌈iterationThreshold (1 - (2 * (1 - κ))⁻¹) (tStar - t 0) ((1 - κ) * ε)⌉₊`.
theorem constrainedMinimization_error_le_target_at_natCeil_iterationThreshold
    {ε : ℝ} (hκ_contract : 1 < 2 * (1 - κ)) (hε : 0 < ε)
    (hstep :
      ∀ n : ℕ, tStar - t (n + 1) ≤ (tStar - t n) / (2 * (1 - κ))) :
    tStar -
        t ⌈Real.log ((tStar - t 0) / ((1 - κ) * ε)) / Real.log (2 * (1 - κ))⌉₊ ≤
      (1 - κ) * ε := by
  have hresidual := residual_hasGeometricRateOfConvergence hκ_contract hstep
  have htarget_pos : 0 < (1 - κ) * ε := by
    have hone_sub_kappa_pos : 0 < 1 - κ := by
      nlinarith
    positivity
  have hnatCeil :
      residual ⌈iterationThreshold (1 - (2 * (1 - κ))⁻¹) (tStar - t 0) ((1 - κ) * ε)⌉₊ ≤
        (1 - κ) * ε := by
    simpa using
      le_target_at_natCeil_iterationThreshold hresidual (owner_contract hκ_contract) htarget_pos
  change
    residual ⌈Real.log ((tStar - t 0) / ((1 - κ) * ε)) / Real.log (2 * (1 - κ))⌉₊ ≤
      (1 - κ) * ε
  rw [residual_iterationThreshold_eq_textbook]
    at hnatCeil
  exact hnatCeil

end

end

/-! ### Theorem_2_29 (from Chap02) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 2.29 lies in first-order optimality for convex minimization on a real inner-product
space.

Sampled owner-style declarations before refining this file:
* mathlib `ConvexOn`
* mathlib `IsMinOn`
* `ConvexOn.lower_tangent_plane` in `Definition_2_2`, the chapter owner theorem for the
  first-order support inequality on a convex set
* `DifferentiableAt.hasGradientAt`, the canonical bridge from the source differentiability
  hypothesis to an explicit gradient witness
* `IsMinOn.isGLB` in mathlib, a canonical minimizer consequence later reused from this owner
  theorem

Best owner abstraction:
* `ConvexOn ℝ Q f` together with `IsMinOn f Q xStar`

Primitive data:
* the feasible set `Q`
* the objective `f`
* the feasible point `xStar`
* convexity of `f` on `Q`
* the constrained minimizing predicate `IsMinOn f Q xStar`

Derived API:
* the supporting-hyperplane inequality from `ConvexOn.lower_tangent_plane`
* the owner theorem `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt`
* the source-facing specialization obtained from `DifferentiableAt.hasGradientAt`

Source/core/bridge triage:
* source-facing: Theorem 2.29 as the variational characterization of constrained optimality using
  the ambient gradient `∇ f xStar`
* core/canonical: `ConvexOn ℝ Q f`, `HasGradientAt f g xStar`, and `IsMinOn f Q xStar`
* bridge/view: the source differentiability hypothesis specialized via
  `DifferentiableAt.hasGradientAt`
-/

namespace ConvexOn

variable {Q : Set E} {f : E → ℝ} {xStar g : E}

/-- A feasible point minimizes a convex function on `Q` exactly when every feasible displacement
has nonnegative pairing with an ambient gradient witness at that point. -/
-- Proof sketch: the forward implication combines `ConvexOn.lower_tangent_plane` at `xStar` with
-- the minimizing property to force nonnegative pairing against every feasible displacement. For
-- the reverse implication, restrict `f` to the segment from `xStar` to `x`; convexity gives a
-- one-variable convex function with a minimum at `0`, and `hf_grad` identifies its derivative
-- there with `inner ℝ g (x - xStar)`.
theorem isMinOn_iff_variational_inequality_of_hasGradientAt
    (hf_conv : ConvexOn ℝ Q f) (hxStar : xStar ∈ Q) (hf_grad : HasGradientAt f g xStar) :
    IsMinOn f Q xStar ↔ ∀ x ∈ Q, 0 ≤ inner ℝ g (x - xStar) := by
  constructor
  · intro hopt x hx
    -- Every feasible displacement comes from a segment inside `Q`, so it is a valid tangent
    -- direction for the localized minimizing property at `xStar`.
    have hdir : x - xStar ∈ posTangentConeAt Q xStar := by
      exact sub_mem_posTangentConeAt_of_segment_subset (hf_conv.1.segment_subset hxStar hx)
    -- Localizing the constrained minimum turns the gradient witness into a nonnegative directional
    -- derivative along that feasible direction.
    have hfirstOrder :=
      hopt.localize.hasFDerivWithinAt_nonneg hf_grad.hasFDerivAt.hasFDerivWithinAt hdir
    -- The derivative supplied by `HasGradientAt` evaluates to the ambient inner product.
    simpa [hf_grad.hasFDerivAt.fderiv, innerSL_apply_apply] using hfirstOrder
  · intro hvari
    rw [isMinOn_iff]
    intro x hx
    -- Turn the ambient gradient witness into the corresponding within-set witness at `xStar`.
    have hgradWithin : HasGradientWithinAt f g Q xStar := by
      convert
        (hf_grad.hasFDerivAt.hasFDerivWithinAt.hasGradientWithinAt :
          HasGradientWithinAt f _ Q xStar) using 1
      simp
    -- Convexity gives the tangent-plane lower bound at `xStar`.
    have hplane :=
      hf_conv.lower_tangent_plane_of_hasGradientWithinAt xStar hxStar g
        hgradWithin x hx
    -- The assumed variational inequality makes the tangent correction term nonnegative.
    have hpair : 0 ≤ inner ℝ g (x - xStar) := hvari x hx
    linarith

end ConvexOn

namespace ConvexOn

variable {Q : Set E} {f : E → ℝ} {xStar : E}

/-- Theorem 2.29: for a convex function `f` on `Q` that is differentiable at the feasible point
`xStar`, constrained optimality at `xStar` is equivalent to the variational inequality
`⟪∇ f xStar, x - xStar⟫ ≥ 0` for every `x ∈ Q`. -/
-- Proof sketch: specialize the preceding owner theorem using the canonical gradient
-- witness `hf_diff.hasGradientAt`.
theorem isMinOn_iff_gradient_variational_inequality
    (hf_conv : ConvexOn ℝ Q f) (hxStar : xStar ∈ Q) (hf_diff : DifferentiableAt ℝ f xStar) :
    IsMinOn f Q xStar ↔ ∀ x ∈ Q, 0 ≤ inner ℝ (∇ f xStar) (x - xStar) :=
  hf_conv.isMinOn_iff_variational_inequality_of_hasGradientAt hxStar hf_diff.hasGradientAt

end ConvexOn

end
