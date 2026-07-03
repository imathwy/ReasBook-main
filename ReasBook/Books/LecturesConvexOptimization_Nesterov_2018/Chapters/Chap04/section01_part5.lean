import Mathlib
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_4_1_3 (from Chap04) -/
open scoped Gradient
open scoped LevelSetNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 4.1.3 lies in the cubic-regularization / Hessian-Lipschitz descent domain.

Sampled owner declarations:
* `HessianLipschitzOn` in `Definition_4_1_2`
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`
* `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y` in `Definition_4_1_3`
* `regularizedHessian_isPositive_of_isMinOn_cubicRegularizationQuadraticApproximation` in
  `Lemma_4_1_2`
* `𝓛[f](α)` together with `mem_levelSet_iff` in `Definition_4_1_1`

Source/core/bridge triage:
* source-facing: the inner-product inequality `(4.1.9)` and the sharper
  `M > (2 / 3) L` level-set/feasibility conclusion of Lemma 4.1.3
* core/canonical: `HessianLipschitzOn`, `cubicRegularizationQuadraticApproximation`,
  `IsMinOn ... Set.univ ...`, and the chapter sublevel-set owner `𝓛[f]((f x))`
* bridge/view: the passage from sublevel membership to feasibility through the ambient inclusion
  `𝓛[f]((f x)) ⊆ 𝓕`

Primitive data:
* the feasible region `𝓕`
* the Hessian-Lipschitz owner `[HessianLipschitzOn L 𝓕 f]`
* the cubic-model minimizer hypothesis
  `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint`
* for the inner-product inequality `(4.1.9)`, the base point membership `x ∈ 𝓕`
* the source threshold `((2 / 3 : ℝ) * (L : ℝ) < M)`
* the current-sublevel inclusion `𝓛[f]((f x)) ⊆ 𝓕`, which is the primitive chapter context
  behind the textbook phrase `𝓛(f(x)) ⊂ 𝓕`; this already implies `x ∈ 𝓕` because
  `x ∈ 𝓛[f]((f x))`

Derived API:
* the source inequality `⟪∇ f(x), x - T_M(x)⟫ ≥ 0`
* the source level-set/feasibility conclusion for the cubic trial point

The previous refinement narrowed the main theorem to the stronger owner bound `L ≤ M` and only the
ambient sublevel inequality. This file restores the sharper source-facing threshold
`M > (2 / 3) L` and keeps the level-set/feasibility conclusion as the main public entry, while
still using the chapter’s canonical minimizer and sublevel owners on the theorem surface. -/

section

variable {𝓕 : Set E} {f : E → ℝ} {L : NNReal} {M : ℝ} {x trialPoint : E}

/-- Helper for Lemma 4.1.3: the scalar first-order optimality condition along the segment from
`x` to the minimizing trial point rewrites the gradient pairing as the regularized quadratic
form from the source proof. -/
lemma gradient_pairing_eq_regularized_quadratic_form
    [HessianLipschitzOn L 𝓕 f]
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hx : x ∈ 𝓕) :
    inner ℝ (∇ f x) (x - trialPoint) =
      inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) +
        (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
  -- TODO: recover the textbook stationarity identity by differentiating the cubic model along the
  -- affine line `α ↦ x + α • (trialPoint - x)` at `α = 1`.
  sorry

/-- Helper for Lemma 4.1.3: the missing source inequality
`⟪∇²f(x)(trialPoint - x), trialPoint - x⟫ + (M / 2) ‖trialPoint - x‖^3 ≥ 0` is the scalar
regularized-Hessian positivity input used immediately after the stationarity identity. -/
lemma regularized_quadratic_form_nonneg
    [HessianLipschitzOn L 𝓕 f]
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hx : x ∈ 𝓕) :
    0 ≤ inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) +
      (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
  -- TODO: supply the missing regularized-Hessian positivity route from Lemma 4.1.2, or prove
  -- this scalar inequality directly by a local replacement of the same source step.
  sorry

/-- Lemma 4.1.3, inequality `(4.1.9)`: for a minimizing cubic trial point, the displacement
`x - trialPoint` has nonnegative pairing with the gradient at the base point `x`. Specializing to
`trialPoint = T_M(x)` recovers the textbook formula. -/
theorem inner_gradient_base_sub_cubicTrialPoint_nonneg
    [HessianLipschitzOn L 𝓕 f]
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hx : x ∈ 𝓕) :
    0 ≤ inner ℝ (∇ f x) (x - trialPoint) := by
  -- Route correction: first rewrite the pairing by the stationarity identity, then discharge the
  -- resulting scalar form by the regularized-Hessian nonnegativity input.
  have hpair :=
    gradient_pairing_eq_regularized_quadratic_form (L := L) (𝓕 := 𝓕) (f := f)
      (M := M) (x := x) (trialPoint := trialPoint) hstep hx
  simpa [hpair] using
    regularized_quadratic_form_nonneg (L := L) (𝓕 := 𝓕) (f := f)
      (M := M) (x := x) (trialPoint := trialPoint) hstep hx

/-- Helper for Lemma 4.1.3: every feasible point on the segment from `x` to the minimizing trial
point satisfies the source cubic-decrease estimate. -/
lemma segment_objective_drop_of_mem_feasible
    [HessianLipschitzOn L 𝓕 f]
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hx : x ∈ 𝓕)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hz : x + α • (trialPoint - x) ∈ 𝓕) :
    f (x + α • (trialPoint - x)) ≤
      f x - α ^ (2 : ℕ) * (M / 4 - α * (L : ℝ) / 6) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
  let z : E := x + α • (trialPoint - x)
  have herror :=
    HessianLipschitzOn.secondOrderTaylorModel_error_le
      (hf := (inferInstance : HessianLipschitzOn L 𝓕 f)) x z hx hz
  -- First replace `f z` by the quadratic Taylor model plus the cubic Hessian-Lipschitz error.
  have hupper :
      f z ≤ secondOrderTaylorModelAt f x z + ((L : ℝ) / 6) * ‖z - x‖ ^ (3 : ℕ) := by
    linarith [(abs_le.mp herror).2]
  have hpair :=
    gradient_pairing_eq_regularized_quadratic_form (L := L) (𝓕 := 𝓕) (f := f)
      (M := M) (x := x) (trialPoint := trialPoint) hstep hx
  have hnonneg :=
    inner_gradient_base_sub_cubicTrialPoint_nonneg (L := L) (𝓕 := 𝓕) (f := f)
      (M := M) (x := x) (trialPoint := trialPoint) hstep hx
  have hzsub : z - x = α • (trialPoint - x) := by
    dsimp [z]
    abel_nf
  have hquad_scale :
      inner ℝ (hessian f x (α • (trialPoint - x))) (α • (trialPoint - x)) =
        α ^ (2 : ℕ) * inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) := by
    simp [inner_smul_left, inner_smul_right, pow_two, mul_assoc]
  have hgrad_flip :
      inner ℝ (∇ f x) (x - trialPoint) = - inner ℝ (∇ f x) (trialPoint - x) := by
    rw [show x - trialPoint = -(trialPoint - x) by abel_nf, inner_neg_right]
  have hpair' :
      inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) =
        - inner ℝ (∇ f x) (trialPoint - x) - (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
    linarith [hpair, hgrad_flip]
  -- Then rewrite the Taylor model exactly as in the source proof.
  have hmodel :
      secondOrderTaylorModelAt f x z + ((L : ℝ) / 6) * ‖z - x‖ ^ (3 : ℕ) =
        f x + (α - α ^ (2 : ℕ) / 2) * inner ℝ (∇ f x) (trialPoint - x) -
          α ^ (2 : ℕ) * (M / 4 - α * (L : ℝ) / 6) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
    rw [secondOrderTaylorModelAt_apply, hzsub, inner_smul_right, hquad_scale, hpair', norm_smul,
      Real.norm_of_nonneg hα.1, mul_pow]
    ring
  rw [hmodel] at hupper
  have hcoef : 0 ≤ α - α ^ (2 : ℕ) / 2 := by
    nlinarith [hα.1, hα.2]
  have hgrad_nonpos : inner ℝ (∇ f x) (trialPoint - x) ≤ 0 := by
    have hgrad_neg :
        inner ℝ (∇ f x) (trialPoint - x) = - inner ℝ (∇ f x) (x - trialPoint) := by
      rw [show trialPoint - x = -(x - trialPoint) by abel_nf, inner_neg_right]
    rw [hgrad_neg]
    exact neg_nonpos.mpr hnonneg
  have hdrop_linear :
      (α - α ^ (2 : ℕ) / 2) * inner ℝ (∇ f x) (trialPoint - x) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos hcoef hgrad_nonpos
  linarith

/-- Helper for Lemma 4.1.3: once every feasible point on the segment from `x` to `trialPoint`
falls back into the current sublevel set, the source first-exit argument should force the whole
segment to stay feasible. -/
lemma segment_feasible_of_sublevel_containment
    (hsublevel : 𝓛[f]((f x)) ⊆ 𝓕)
    (hsegment :
      ∀ {α : ℝ}, α ∈ Set.Icc (0 : ℝ) 1 →
        x + α • (trialPoint - x) ∈ 𝓕 →
        x + α • (trialPoint - x) ∈ 𝓛[f]((f x))) :
    trialPoint ∈ 𝓕 := by
  -- Route correction: the remaining gap is not the cubic-model algebra but the interval
  -- first-exit argument that upgrades pointwise feasible-segment sublevel control to endpoint
  -- feasibility.
  -- TODO: package the `Lemma_4_4_4` clopen-on-`Icc` architecture here. The blocker is proving the
  -- relevant segment preimage is closed from the current dependency closure, since the available
  -- `HessianLipschitzOn` hypothesis only gives continuity of `f` on `𝓕`, not on the whole
  -- segment a priori.
  sorry

/-- Lemma 4.1.3: if the current sublevel set `𝓛(f(x))` is contained in `𝓕`,
`f` has `L`-Lipschitz Hessian on `𝓕`, a point `trialPoint` globally minimizes the chapter cubic
model centered at `x`, and `M > (2 / 3) L`, then `trialPoint` belongs to the sublevel set
`𝓛[f]((f x))` and hence is feasible. Specializing to `trialPoint = T_M(x)` recovers the
textbook statement. -/
theorem cubicTrialPoint_mem_sublevel_and_feasible
    [HessianLipschitzOn L 𝓕 f]
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hsublevel : 𝓛[f]((f x)) ⊆ 𝓕)
    (hM : (2 / 3 : ℝ) * (L : ℝ) < M) :
    trialPoint ∈ 𝓛[f]((f x)) ∧ trialPoint ∈ 𝓕 := by
  have hx : x ∈ 𝓕 := by
    apply hsublevel
    rw [mem_levelSet_iff]
  -- Every feasible segment point satisfies the source objective decrease, hence lies in the
  -- current sublevel set.
  have hsegment :
      ∀ {α : ℝ}, α ∈ Set.Icc (0 : ℝ) 1 →
        x + α • (trialPoint - x) ∈ 𝓕 →
        x + α • (trialPoint - x) ∈ 𝓛[f]((f x)) := by
    intro α hα hz
    have hdrop :=
      segment_objective_drop_of_mem_feasible (L := L) (𝓕 := 𝓕) (f := f)
        (M := M) (x := x) (trialPoint := trialPoint) hstep hx hα hz
    have hcoef : 0 ≤ M / 4 - α * (L : ℝ) / 6 := by
      nlinarith [hM, hα.1, hα.2]
    have hpow : 0 ≤ ‖trialPoint - x‖ ^ (3 : ℕ) := by
      positivity
    have hαsq : 0 ≤ α ^ (2 : ℕ) := by
      positivity
    have hterm_nonneg :
        0 ≤ α ^ (2 : ℕ) * (M / 4 - α * (L : ℝ) / 6) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
      positivity
    rw [mem_levelSet_iff]
    linarith
  -- The only remaining source step is the first-exit argument along the segment.
  have htrial_feasible :
      trialPoint ∈ 𝓕 :=
    segment_feasible_of_sublevel_containment (f := f) (𝓕 := 𝓕)
      (x := x) (trialPoint := trialPoint) hsublevel hsegment
  have htrial_sublevel : trialPoint ∈ 𝓛[f]((f x)) := by
    have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    have hfeas1 : x + (1 : ℝ) • (trialPoint - x) ∈ 𝓕 := by
      simpa using htrial_feasible
    simpa using hsegment h1 hfeas1
  exact ⟨htrial_sublevel, htrial_feasible⟩

/-- Companion bridge: the source-facing theorem yields the ambient sublevel inequality
`f trialPoint ≤ f x`. -/
theorem cubicTrialPoint_mem_sublevel
    [HessianLipschitzOn L 𝓕 f]
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hsublevel : 𝓛[f]((f x)) ⊆ 𝓕)
    (hM : (2 / 3 : ℝ) * (L : ℝ) < M) :
    trialPoint ∈ 𝓛[f]((f x)) :=
  (cubicTrialPoint_mem_sublevel_and_feasible hstep hsublevel hM).1

end

/-! ### Proposition_4_1_3 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Proposition 4.1.3 lies in first-order convex analysis on a real Hilbert space.

Sampled owner-style declarations:
* `ConvexOn.lower_tangent_plane` in `Chap02/Definition_2_2`
* `isMinOn_iff_eq_sInf_range` in `Chap03/Definition_3_33`
* mathlib `real_inner_le_norm`

Best owner abstraction:
* `ConvexOn ℝ Set.univ f`

Primitive data:
* the objective `f`
* whole-space convexity of `f`
* differentiability of `f` at the base point where the gradient is evaluated
* for the source-facing proposition, a chosen global minimizer `xStar` witnessing that the
  canonical optimal value `sInf (Set.range f)` is attained

Derived API:
* the first-order support inequality from `ConvexOn.lower_tangent_plane`
* the radius estimate from Cauchy--Schwarz
* the sharper comparison-point gap estimate on a closed ball
* the optimal-value identity `sInf (Set.range f) = f xStar` from
  `isMinOn_iff_eq_sInf_range`

Source/core/bridge triage:
* source-facing: the suboptimality bound relative to the canonical optimal value, witnessed by a
  chosen minimizer
* core/canonical: `ConvexOn.lower_tangent_plane`
* bridge/view: the comparison-point estimate obtained by specializing that owner theorem to
  `Set.univ` and combining it with `real_inner_le_norm`, together with the attained-infimum bridge
  `isMinOn_iff_eq_sInf_range`

The main proposition now records the suboptimality gap against the canonical optimal value
`sInf (Set.range f)`, so the minimizer witness is mathematically active rather than an unused
binder. The sharper owner-level comparison estimate is retained only as a companion theorem.
-/
namespace ConvexOn

/-- Helper for Proposition 4.1.3: for a convex function on a real Hilbert space that is
differentiable at the base point `x`, the objective gap to any comparison point within distance at
most `R` from `x` is bounded by `R` times the gradient norm at `x`. -/
-- Proof sketch: apply `ConvexOn.lower_tangent_plane` at the base point `x` and comparison point
-- `y`, rewrite the resulting support inequality as a bound on `f x - f y`, and then use
-- Cauchy--Schwarz together with `‖x - y‖ ≤ R`.
theorem gap_le_radius_mul_norm_gradient_of_dist_le
    {f : E → ℝ} (hf_conv : ConvexOn ℝ Set.univ f) {x : E} (hf_diff : DifferentiableAt ℝ f x)
    {y : E} {R : ℝ}
    (hxy : ‖x - y‖ ≤ R) :
    f x - f y ≤ R * ‖∇ f x‖ := by
  have hsupport :
      f y ≥ f x + inner ℝ (∇ f x) (y - x) := by
    simpa [gradientWithin, gradient, fderivWithin_univ] using
      hf_conv.lower_tangent_plane x (by simp) hf_diff.differentiableWithinAt y (by simp)
  have hfirst : f x - f y ≤ inner ℝ (∇ f x) (x - y) := by
    have hinner :
        inner ℝ (∇ f x) (y - x) = -inner ℝ (∇ f x) (x - y) := by
      calc
        inner ℝ (∇ f x) (y - x) = inner ℝ (∇ f x) (-(x - y)) := by
          congr 2
          abel
        _ = -inner ℝ (∇ f x) (x - y) := by
          rw [inner_neg_right]
    linarith
  calc
    f x - f y ≤ inner ℝ (∇ f x) (x - y) := hfirst
    _ ≤ ‖∇ f x‖ * ‖x - y‖ := real_inner_le_norm _ _
    _ ≤ ‖∇ f x‖ * R := mul_le_mul_of_nonneg_left hxy (norm_nonneg _)
    _ = R * ‖∇ f x‖ := by ring

end ConvexOn

/-- Proposition 4.1.3: if `f` is convex, `xStar` is a global minimizer of `f`, and `f` is
differentiable at a point `x` lying in the closed ball of radius `R` around `xStar`, then the
suboptimality gap above the optimal value `sInf (Set.range f)` is bounded by `R * ‖∇ f x‖`.
Since `xStar` attains that infimum, this is equivalent to the textbook form
`f x - f xStar ≤ R * ‖∇ f x‖`. -/
-- Proof sketch: use the Chapter 3 owner bridge `isMinOn_iff_eq_sInf_range` to rewrite the
-- canonical optimal value `sInf (Set.range f)` as `f xStar`, then apply the comparison-point
-- estimate with `y = xStar`.
theorem convex_suboptimality_le_radius_mul_norm_gradient
    (f : E → ℝ) (hf_conv : ConvexOn ℝ Set.univ f)
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar) {x : E} (hf_diff : DifferentiableAt ℝ f x)
    {R : ℝ}
    (hx : ‖x - xStar‖ ≤ R) :
    f x - sInf (Set.range f) ≤ R * ‖∇ f x‖ := by
  have hsInf_eq : sInf (Set.range f) = f xStar := by
    have hbelow : BddBelow (Set.range f) := ⟨f xStar, by
      rintro _ ⟨y, rfl⟩
      exact hxStar (by simp)
    ⟩
    exact ((isMinOn_iff_eq_sInf_range hbelow).1 hxStar).symm
  rw [hsInf_eq]
  exact hf_conv.gap_le_radius_mul_norm_gradient_of_dist_le hf_diff hx

end

/-! ### Theorem_4_1_3_1 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace RelaxedRegularizedNewtonIteration

variable {stepMap : ℝ → E → E} {L : ℝ}

/-- The primitive cubic-regularization assumptions needed already for Theorem 4.1.3.1 along a
fixed relaxed regularized Newton trajectory. The later recurrence and summability consequences in
this theorem are derived API from this owner. -/
class HasCubicRegularizationRecurrenceHypotheses
    (method : RelaxedRegularizedNewtonIteration stepMap L) (f : E → ℝ) : Prop where
  /-- The initial least Hessian eigenvalue is positive. -/
  lambda0_pos : 0 < λ_min(∇²f(method 0))
  /-- The initial cubic-regularization decrement satisfies the textbook bootstrap bound
  `δ₀ ≤ 1 / 4`. -/
  delta0_le_quarter : cubicRegularizationDelta f (method 0) L ≤ (1 / 4 : ℝ)
  /-- The step length is controlled by the gradient norm and least Hessian eigenvalue. -/
  step_norm (k : ℕ) :
      ‖method (k + 1) - method k‖ ≤
        ‖∇ f (method k)‖ / λ_min(∇²f(method k))
  /-- The least Hessian eigenvalue obeys the one-step lower comparison. -/
  lambda_succ (k : ℕ) :
      λ_min(∇²f(method (k + 1))) ≥
        λ_min(∇²f(method k)) - L * ‖method (k + 1) - method k‖
  /-- The next gradient norm is bounded by the cubic-model error term. -/
  gradient_succ (k : ℕ) :
      ‖∇ f (method (k + 1))‖ ≤
        ((L + method.regularization k) / 2) * ‖method (k + 1) - method k‖ ^ (2 : ℕ)

/-- The full cubic-regularization theorem-family assumptions extend the recurrence owner from
Theorem 4.1.3.1 by the symmetric upper Hessian comparison needed in Theorem 4.1.3.2. -/
class HasCubicRegularizationHypotheses
    (method : RelaxedRegularizedNewtonIteration stepMap L) (f : E → ℝ) : Prop
    extends HasCubicRegularizationRecurrenceHypotheses method f where
  /-- The least Hessian eigenvalue obeys the one-step upper comparison coming from the same
  Hessian-Lipschitz control. -/
  lambda_succ_upper (k : ℕ) :
      λ_min(∇²f(method (k + 1))) ≤
        λ_min(∇²f(method k)) + L * ‖method (k + 1) - method k‖

end RelaxedRegularizedNewtonIteration

/- Theorem 4.1.3.1 lies in the cubic-regularization decrement-recurrence domain.

Sampled owner declarations:
* `RelaxedRegularizedNewtonIteration` in `Definition_4_1_5`, the chapter owner for the iterate
  sequence, regularization schedule, and admissible parameter range;
* `cubicRegularizationDelta` in `Definition_4_1_6`, the chapter owner for the decrement
  `L ‖∇f(x)‖ / λ_min(∇²f(x))^2`;
* `hessianLeastEigenvalue` in `Definition_4_1_6`, the owner for `λ_min(∇² f x)`;
* `HasEventuallySuperlinearErrorBound` in `Chap01/Definition_1_2_7`, the project owner for the
  quadratic scalar recurrence conclusion;
* `method.HasCubicRegularizationRecurrenceHypotheses f`, the source-facing owner for the
  assumptions used already in Theorem 4.1.3.1;
* `method.HasCubicRegularizationHypotheses f`, the extended theorem-family owner used later when
  the upper spectral envelope is needed.

Best owner abstraction:
* source-facing: the recurrence statements for the decrement sequence along a relaxed
  cubic-regularization trajectory;
* core/canonical: `RelaxedRegularizedNewtonIteration`,
  `method.HasCubicRegularizationRecurrenceHypotheses f`,
  `cubicRegularizationDelta`, and `HasEventuallySuperlinearErrorBound`;
* bridge/view: the local notation `δ`, which packages the decrement owner along the trajectory.

Primitive data:
* the objective `f`,
* the relaxed regularized Newton trajectory `method`,
* the recurrence hypothesis owner attached to `(method, f)`.

Derived API:
* positivity of the least Hessian eigenvalue along the trajectory,
* the one-step decrement recurrence,
* the quadratic and linear one-step corollaries,
* the canonical quadratic-rate witness,
* summability and total-sum consequences for the decrement sequence.
-/

section

open RelaxedRegularizedNewtonIteration

variable (L : ℝ) (f : E → ℝ) {stepMap : ℝ → E → E}
variable (method : RelaxedRegularizedNewtonIteration stepMap L)

local notation "δ" => fun k : ℕ ↦ cubicRegularizationDelta f (method k) L

/-- Helper for Theorem 4.1.3.1: every cubic-regularization decrement is nonnegative because it is
`L` times a norm divided by a square. -/
lemma cubicRegularizationDelta_nonneg
    (x : E) (hL : 0 ≤ L) :
    0 ≤ cubicRegularizationDelta f x L := by
  -- Unfold the decrement and use nonnegativity of the norm, the scalar `L`, and the squared
  -- denominator.
  rw [cubicRegularizationDelta_def]
  exact div_nonneg (mul_nonneg hL (norm_nonneg _)) (sq_nonneg _)

/-- Helper for Theorem 4.1.3.1: the raw step bound rewrites into the source estimate
`‖x_{k+1} - x_k‖ ≤ (λ_k / L) δ_k`. -/
lemma cubicRegularization_step_norm_le_lambda_mul_delta
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) (hLambda_k : 0 < λ_min(∇²f(method k))) :
    ‖method (k + 1) - method k‖ ≤
      (λ_min(∇²f(method k)) / L) * δ k := by
  have hL : 0 < L := method.L_pos
  have hdelta_k :
      δ k = L * ‖∇ f (method k)‖ / λ_min(∇²f(method k)) ^ (2 : ℕ) := by
    exact cubicRegularizationDelta_def f (method k) L
  -- Rewrite the raw norm bound exactly into the decrement form used in the source proof.
  calc
    ‖method (k + 1) - method k‖
        ≤ ‖∇ f (method k)‖ / λ_min(∇²f(method k)) :=
      hmethod.step_norm k
    _ = (λ_min(∇²f(method k)) / L) * δ k := by
      rw [hdelta_k]
      field_simp [hL.ne', hLambda_k.ne']

/-- Helper for Theorem 4.1.3.1: the one-step Hessian comparison yields
`(1 - δ_k) λ_k ≤ λ_{k+1}`. -/
lemma cubicRegularization_lambda_succ_ge_one_sub_delta_mul
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) (hLambda_k : 0 < λ_min(∇²f(method k))) :
    (1 - δ k) * λ_min(∇²f(method k)) ≤
      λ_min(∇²f(method (k + 1))) := by
  have hL : 0 < L := method.L_pos
  have hstep :=
    cubicRegularization_step_norm_le_lambda_mul_delta
      (L := L) (f := f) (method := method) hmethod k hLambda_k
  have hmul :
      L * ‖method (k + 1) - method k‖ ≤
        L * ((λ_min(∇²f(method k)) / L) * δ k) := by
    exact mul_le_mul_of_nonneg_left hstep hL.le
  have hsub :
      λ_min(∇²f(method k)) - L * ((λ_min(∇²f(method k)) / L) * δ k) ≤
        λ_min(∇²f(method k)) - L * ‖method (k + 1) - method k‖ := by
    exact sub_le_sub_left hmul _
  -- Substitute the rewritten step estimate into the Hessian lower comparison.
  calc
    (1 - δ k) * λ_min(∇²f(method k))
        = λ_min(∇²f(method k)) - L * ((λ_min(∇²f(method k)) / L) * δ k) := by
      field_simp [hL.ne']
    _ ≤ λ_min(∇²f(method k)) - L * ‖method (k + 1) - method k‖ :=
      hsub
    _ ≤ λ_min(∇²f(method (k + 1))) :=
      hmethod.lambda_succ k

/-- Helper for Theorem 4.1.3.1: under the bootstrap hypotheses
`λ_k > 0` and `δ_k ≤ 1 / 4`, the source fraction recurrence already holds at the next step. -/
lemma cubicRegularization_delta_step_le_fraction_of_quarter_bound
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) (hLambda_k : 0 < λ_min(∇²f(method k))) (hδk : δ k ≤ (1 / 4 : ℝ)) :
    δ (k + 1) ≤ (3 / 2 : ℝ) * (δ k / (1 - δ k)) ^ (2 : ℕ) := by
  have hL : 0 < L := method.L_pos
  have hd_nonneg : 0 ≤ δ k :=
    cubicRegularizationDelta_nonneg (L := L) (f := f) (x := method k) hL.le
  have hone_sub_nonneg : 0 ≤ 1 - δ k := by
    linarith
  have hone_sub_pos : 0 < 1 - δ k := by
    linarith
  have hLambda_succ_lower :=
    cubicRegularization_lambda_succ_ge_one_sub_delta_mul
      (L := L) (f := f) (method := method) hmethod k hLambda_k
  have hLambda_succ_pos : 0 < λ_min(∇²f(method (k + 1))) := by
    -- The bootstrap inequality keeps the least Hessian eigenvalue strictly positive.
    exact lt_of_lt_of_le (mul_pos hone_sub_pos hLambda_k) hLambda_succ_lower
  have hreg :
      (L + method.regularization k) / 2 ≤ (3 / 2 : ℝ) * L := by
    have hMk := method.regularization_le_two_mul_L k
    linarith
  have hgrad :
      ‖∇ f (method (k + 1))‖ ≤
        ((3 / 2 : ℝ) * L) * ‖method (k + 1) - method k‖ ^ (2 : ℕ) := by
    -- Replace the variable regularization parameter by the uniform bound `2L`.
    calc
      ‖∇ f (method (k + 1))‖
          ≤ ((L + method.regularization k) / 2) *
              ‖method (k + 1) - method k‖ ^ (2 : ℕ) :=
        hmethod.gradient_succ k
      _ ≤ ((3 / 2 : ℝ) * L) * ‖method (k + 1) - method k‖ ^ (2 : ℕ) := by
        have hsq_nonneg : 0 ≤ ‖method (k + 1) - method k‖ ^ (2 : ℕ) := by
          positivity
        exact mul_le_mul_of_nonneg_right hreg hsq_nonneg
  have hstep :=
    cubicRegularization_step_norm_le_lambda_mul_delta
      (L := L) (f := f) (method := method) hmethod k hLambda_k
  have hstep_scaled :
      L * ‖method (k + 1) - method k‖ ≤
        λ_min(∇²f(method k)) * δ k := by
    have hmul : L * ‖method (k + 1) - method k‖ ≤
        L * ((λ_min(∇²f(method k)) / L) * δ k) := by
      exact mul_le_mul_of_nonneg_left hstep hL.le
    calc
      L * ‖method (k + 1) - method k‖
          ≤ L * ((λ_min(∇²f(method k)) / L) * δ k) :=
        hmul
      _ = λ_min(∇²f(method k)) * δ k := by
        field_simp [hL.ne']
  have hcross_left :
      (L * ‖method (k + 1) - method k‖) * (1 - δ k) ≤
        (λ_min(∇²f(method k)) * δ k) * (1 - δ k) := by
    exact mul_le_mul_of_nonneg_right hstep_scaled hone_sub_nonneg
  have hcross_right :
      (λ_min(∇²f(method k)) * δ k) * (1 - δ k) ≤
        δ k * λ_min(∇²f(method (k + 1))) := by
    have hmul := mul_le_mul_of_nonneg_left hLambda_succ_lower hd_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hcross :
      (L * ‖method (k + 1) - method k‖) * (1 - δ k) ≤
        λ_min(∇²f(method (k + 1))) * δ k := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcross_left.trans hcross_right
  have hratio :
      L * ‖method (k + 1) - method k‖ / λ_min(∇²f(method (k + 1))) ≤
        δ k / (1 - δ k) := by
    -- Cross-multiplication is legitimate because both denominators are strictly positive.
    field_simp [hLambda_succ_pos.ne', hone_sub_pos.ne']
    exact hcross
  have hratio_nonneg :
      0 ≤ L * ‖method (k + 1) - method k‖ / λ_min(∇²f(method (k + 1))) := by
    exact div_nonneg (mul_nonneg hL.le (norm_nonneg _)) hLambda_succ_pos.le
  have hratio_rhs_nonneg : 0 ≤ δ k / (1 - δ k) := by
    exact div_nonneg hd_nonneg hone_sub_nonneg
  have hratio_sq :
      (L * ‖method (k + 1) - method k‖ / λ_min(∇²f(method (k + 1)))) ^ (2 : ℕ) ≤
        (δ k / (1 - δ k)) ^ (2 : ℕ) := by
    exact (sq_le_sq₀ hratio_nonneg hratio_rhs_nonneg).2 hratio
  have hdelta_scaled :
      δ (k + 1) ≤
        (3 / 2 : ℝ) *
          (L * ‖method (k + 1) - method k‖ /
            λ_min(∇²f(method (k + 1)))) ^ (2 : ℕ) := by
    -- Rewrite the successor decrement so the numerator and denominator can be controlled
    -- separately by the gradient and Hessian estimates.
    have hdelta_succ :
        δ (k + 1) =
          L * ‖∇ f (method (k + 1))‖ /
            λ_min(∇²f(method (k + 1))) ^ (2 : ℕ) := by
      exact cubicRegularizationDelta_def f (method (k + 1)) L
    rw [hdelta_succ]
    calc
      L * ‖∇ f (method (k + 1))‖ / λ_min(∇²f(method (k + 1))) ^ (2 : ℕ)
          ≤
            L *
              (((3 / 2 : ℝ) * L) * ‖method (k + 1) - method k‖ ^ (2 : ℕ)) /
                λ_min(∇²f(method (k + 1))) ^ (2 : ℕ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hgrad hL.le) (by positivity)
      _ =
          (3 / 2 : ℝ) *
            (L * ‖method (k + 1) - method k‖ /
              λ_min(∇²f(method (k + 1)))) ^ (2 : ℕ) := by
        field_simp [pow_two, hLambda_succ_pos.ne']
  -- The scaled step ratio is now exactly the source fraction recurrence.
  calc
    δ (k + 1)
        ≤
          (3 / 2 : ℝ) *
            (L * ‖method (k + 1) - method k‖ /
              λ_min(∇²f(method (k + 1)))) ^ (2 : ℕ) :=
      hdelta_scaled
    _ ≤ (3 / 2 : ℝ) * (δ k / (1 - δ k)) ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hratio_sq (by norm_num)

/-- Helper for Theorem 4.1.3.1: the source bootstrap invariant simultaneously keeps the least
Hessian eigenvalue positive and the decrement bounded by `1 / 4` at every iterate. -/
lemma cubicRegularization_bootstrap_invariant
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f) :
    ∀ k : ℕ, 0 < λ_min(∇²f(method k)) ∧ δ k ≤ (1 / 4 : ℝ) := by
  intro k
  induction k with
  | zero =>
      -- The initial iterate satisfies the bootstrap assumptions by hypothesis.
      exact ⟨hmethod.lambda0_pos, hmethod.delta0_le_quarter⟩
  | succ k ih =>
      rcases ih with ⟨hLambda_k, hδk⟩
      have hd_nonneg : 0 ≤ δ k :=
        cubicRegularizationDelta_nonneg (L := L) (f := f) (x := method k) (method.L_pos.le)
      have hone_sub_pos : 0 < 1 - δ k := by
        linarith
      have hLambda_succ_lower :=
        cubicRegularization_lambda_succ_ge_one_sub_delta_mul
          (L := L) (f := f) (method := method) hmethod k hLambda_k
      have hLambda_succ : 0 < λ_min(∇²f(method (k + 1))) := by
        -- Positivity propagates because the comparison factor `1 - δ_k` stays positive.
        exact lt_of_lt_of_le (mul_pos hone_sub_pos hLambda_k) hLambda_succ_lower
      have hfraction :=
        cubicRegularization_delta_step_le_fraction_of_quarter_bound
          (L := L) (f := f) (method := method) hmethod k hLambda_k hδk
      have hcoeff :
          (3 / 2 : ℝ) / (1 - δ k) ^ (2 : ℕ) ≤ (8 / 3 : ℝ) := by
        have hmain :
            (3 / 2 : ℝ) ≤ (8 / 3 : ℝ) * (1 - δ k) ^ (2 : ℕ) := by
          nlinarith
        exact (div_le_iff₀ (sq_pos_of_pos hone_sub_pos)).2 hmain
      have hquadratic : δ (k + 1) ≤ (8 / 3 : ℝ) * (δ k) ^ (2 : ℕ) := by
        -- Under `δ_k ≤ 1 / 4`, the source fraction factor is bounded by `16 / 9`.
        calc
          δ (k + 1) ≤ (3 / 2 : ℝ) * (δ k / (1 - δ k)) ^ (2 : ℕ) :=
            hfraction
          _ = ((3 / 2 : ℝ) / (1 - δ k) ^ (2 : ℕ)) * (δ k) ^ (2 : ℕ) := by
            field_simp [pow_two, hone_sub_pos.ne']
          _ ≤ (8 / 3 : ℝ) * (δ k) ^ (2 : ℕ) := by
            exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
      have hlinear : δ (k + 1) ≤ (2 / 3 : ℝ) * δ k := by
        -- The bootstrap bound turns the quadratic recurrence into the advertised linear one.
        have hbound : (8 / 3 : ℝ) * (δ k) ^ (2 : ℕ) ≤ (2 / 3 : ℝ) * δ k := by
          nlinarith
        exact hquadratic.trans hbound
      have hδsucc : δ (k + 1) ≤ (1 / 4 : ℝ) := by
        linarith
      exact ⟨hLambda_succ, hδsucc⟩

/-- Theorem 4.1.3.1 (1): for a relaxed cubic-regularized Newton iteration satisfying the local
step, Hessian, and gradient estimates from the cubic model, the least Hessian eigenvalue stays
positive along the whole iterate sequence. -/
-- Proof sketch: argue by induction on `k`. The step estimate bounds `‖x_{k+1} - x_k‖` by
-- `λ_min(∇² f (x_k)) δ_k / L`; combining this with the Hessian Lipschitz lower bound gives
-- `λ_min(∇² f (x_{k+1})) ≥ (1 - δ_k) λ_min(∇² f (x_k)) > 0`.
theorem cubicRegularization_hessianLeastEigenvalue_pos
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) :
    0 < λ_min(∇²f(method k)) :=
  by
  -- Read off positivity from the first component of the bootstrap invariant.
  exact (cubicRegularization_bootstrap_invariant
    (L := L) (f := f) (method := method) hmethod k).1

/-- Theorem 4.1.3.1 (2): under the cubic-regularization hypotheses, the decrement sequence
satisfies the first displayed one-step bound
`δ_{k+1} ≤ (3 / 2) (δ_k / (1 - δ_k))^2`. -/
-- Proof sketch: use the gradient estimate together with
-- `method.regularization k ≤ 2L`, and rewrite the step-length bound in terms of the decrement
-- `δ_k`.
theorem cubicRegularization_delta_step_le_fraction
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) :
    δ (k + 1) ≤ (3 / 2 : ℝ) * (δ k / (1 - δ k)) ^ (2 : ℕ) :=
  by
  rcases cubicRegularization_bootstrap_invariant
      (L := L) (f := f) (method := method) hmethod k with
    ⟨hLambda_k, hδk⟩
  -- The source fraction recurrence holds once the bootstrap hypotheses at step `k` are known.
  exact cubicRegularization_delta_step_le_fraction_of_quarter_bound
    (L := L) (f := f) (method := method) hmethod k hLambda_k hδk

/-- Theorem 4.1.3.1 (3): under the cubic-regularization hypotheses, the decrement sequence
satisfies the quadratic one-step estimate `δ_{k+1} ≤ (8 / 3) δ_k^2`. -/
-- Proof sketch: combine the first one-step estimate from
-- `cubicRegularization_delta_step_le_fraction` with the bootstrap bound `δ_k ≤ 1 / 4`.
theorem cubicRegularization_delta_step_le_quadratic
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) :
    δ (k + 1) ≤ (8 / 3 : ℝ) * (δ k) ^ (2 : ℕ) :=
  by
  have hδk :=
    (cubicRegularization_bootstrap_invariant
      (L := L) (f := f) (method := method) hmethod k).2
  have hone_sub_pos : 0 < 1 - δ k := by
    linarith
  have hcoeff :
      (3 / 2 : ℝ) / (1 - δ k) ^ (2 : ℕ) ≤ (8 / 3 : ℝ) := by
    have hmain : (3 / 2 : ℝ) ≤ (8 / 3 : ℝ) * (1 - δ k) ^ (2 : ℕ) := by
      nlinarith
    exact (div_le_iff₀ (sq_pos_of_pos hone_sub_pos)).2 hmain
  -- Bound the denominator factor `(1 - δ_k)⁻²` by `16 / 9`.
  calc
    δ (k + 1) ≤ (3 / 2 : ℝ) * (δ k / (1 - δ k)) ^ (2 : ℕ) :=
      cubicRegularization_delta_step_le_fraction
        (L := L) (f := f) (method := method) hmethod k
    _ = ((3 / 2 : ℝ) / (1 - δ k) ^ (2 : ℕ)) * (δ k) ^ (2 : ℕ) := by
      field_simp [pow_two, hone_sub_pos.ne']
    _ ≤ (8 / 3 : ℝ) * (δ k) ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)

/-- Theorem 4.1.3.1 (4): under the cubic-regularization hypotheses, the decrement sequence
satisfies the linear one-step estimate `δ_{k+1} ≤ (2 / 3) δ_k`. -/
-- Proof sketch: combine the quadratic estimate
-- `cubicRegularization_delta_step_le_quadratic` with the bootstrap bound `δ_k ≤ 1 / 4`.
theorem cubicRegularization_delta_step_le_linear
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) :
    δ (k + 1) ≤ (2 / 3 : ℝ) * δ k :=
  by
  have hδk :=
    (cubicRegularization_bootstrap_invariant
      (L := L) (f := f) (method := method) hmethod k).2
  have hd_nonneg : 0 ≤ δ k :=
    cubicRegularizationDelta_nonneg (L := L) (f := f) (x := method k) (method.L_pos.le)
  have hbound : (8 / 3 : ℝ) * (δ k) ^ (2 : ℕ) ≤ (2 / 3 : ℝ) * δ k := by
    nlinarith
  -- The quadratic decay strengthens to linear decay on the bootstrap interval `δ_k ≤ 1 / 4`.
  exact (cubicRegularization_delta_step_le_quadratic
    (L := L) (f := f) (method := method) hmethod k).trans hbound

/-- Helper for Theorem 4.1.3.1: the linear recurrence implies the geometric majorant
`δ_k ≤ δ_0 (2 / 3)^k`. -/
lemma cubicRegularization_delta_le_initial_mul_two_thirds_pow
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f) :
    ∀ k : ℕ, δ k ≤ δ 0 * (2 / 3 : ℝ) ^ k := by
  intro k
  induction k with
  | zero =>
      -- At the initial index, the geometric majorant is exact.
      simp
  | succ k ih =>
      -- Propagate the majorant by one application of the linear decay estimate.
      calc
        δ (k + 1) ≤ (2 / 3 : ℝ) * δ k :=
          cubicRegularization_delta_step_le_linear
            (L := L) (f := f) (method := method) hmethod k
        _ ≤ (2 / 3 : ℝ) * (δ 0 * (2 / 3 : ℝ) ^ k) := by
          exact mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = δ 0 * (2 / 3 : ℝ) ^ (k + 1) := by
          rw [pow_succ]
          ring

/-- Under the hypotheses of Theorem 4.1.3.1, the decrement sequence satisfies the canonical
quadratic-recurrence owner with the textbook constant `8 / 3`. -/
-- Proof sketch: apply `cubicRegularization_delta_step_le_quadratic` and package the same
-- constant `8 / 3` into `HasEventuallySuperlinearErrorBound δ 0 (8 / 3) 0`.
theorem cubicRegularization_delta_hasEventuallySuperlinearErrorBound
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f) :
    HasEventuallySuperlinearErrorBound δ 0 (8 / 3 : ℝ) 0 :=
  by
  -- Package the already proved quadratic recurrence into the canonical owner at lag `0`.
  exact HasEventuallySuperlinearErrorBound.of_quadratic_bound
    (fun k ↦ cubicRegularization_delta_step_le_quadratic
      (L := L) (f := f) (method := method) hmethod k)

/-- Under the hypotheses of Theorem 4.1.3.1, the decrement sequence admits a quadratic recurrence
bound in the source-facing existential form `∃ c > 0, HasEventuallySuperlinearErrorBound δ 0 c 0`.
-/
theorem cubicRegularization_delta_seq_has_quadratic_rate
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f) :
    ∃ c > 0, HasEventuallySuperlinearErrorBound δ 0 c 0 :=
  ⟨8 / 3, by norm_num,
    cubicRegularization_delta_hasEventuallySuperlinearErrorBound L f method hmethod⟩

/-- Under the hypotheses of Theorem 4.1.3.1, the decrement sequence is summable. -/
-- Proof sketch: the estimate `δ_{k+1} ≤ (2 / 3) δ_k` from
-- `cubicRegularization_delta_step_le_linear` compares the decrement sequence with the geometric
-- series of ratio `2 / 3`, which is summable.
theorem cubicRegularization_delta_seq_summable
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f) :
    Summable δ :=
  by
  have hgeom : Summable (fun k : ℕ ↦ (2 / 3 : ℝ) ^ k) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hmajor :
      Summable (fun k : ℕ ↦ δ 0 * (2 / 3 : ℝ) ^ k) :=
    hgeom.mul_left _
  -- Compare the decrement sequence with its geometric majorant.
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro k
    exact cubicRegularizationDelta_nonneg
      (L := L) (f := f) (x := method k) (method.L_pos.le)
  · intro k
    exact cubicRegularization_delta_le_initial_mul_two_thirds_pow
      (L := L) (f := f) (method := method) hmethod k

/-- Under the hypotheses of Theorem 4.1.3.1, the total decrement is bounded by `1 - δ₀`;
equivalently, the textbook geometric-series estimate gives
`∑ δ_k ≤ 3 δ₀ ≤ 1 - δ₀`. -/
-- Proof sketch: use the geometric decay `δ_{k+1} ≤ (2 / 3) δ_k` from
-- `cubicRegularization_delta_step_le_linear` to compare the series with
-- `δ₀ * ∑ (2 / 3)^k = 3 δ₀`, and then use `δ₀ ≤ 1 / 4` to conclude `3 δ₀ ≤ 1 - δ₀`.
theorem tsum_cubicRegularization_delta_seq_le_one_sub_initial
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f) :
    (∑' k, δ k) ≤ 1 - δ 0 :=
  by
  have hgeom : Summable (fun k : ℕ ↦ (2 / 3 : ℝ) ^ k) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hmajor :
      Summable (fun k : ℕ ↦ δ 0 * (2 / 3 : ℝ) ^ k) :=
    hgeom.mul_left _
  have hsum_le :
      (∑' k, δ k) ≤ ∑' k, δ 0 * (2 / 3 : ℝ) ^ k := by
    exact (cubicRegularization_delta_seq_summable
      (L := L) (f := f) (method := method) hmethod).tsum_le_tsum
        (fun k ↦ cubicRegularization_delta_le_initial_mul_two_thirds_pow
          (L := L) (f := f) (method := method) hmethod k)
        hmajor
  have hmajor_tsum :
      (∑' k, δ 0 * (2 / 3 : ℝ) ^ k) = δ 0 * 3 := by
    rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num)]
    norm_num
  -- Evaluate the geometric series and use `δ₀ ≤ 1 / 4` to conclude `3 δ₀ ≤ 1 - δ₀`.
  calc
    (∑' k, δ k) ≤ ∑' k, δ 0 * (2 / 3 : ℝ) ^ k :=
      hsum_le
    _ = δ 0 * 3 := hmajor_tsum
    _ ≤ 1 - δ 0 := by
      nlinarith [hmethod.delta0_le_quarter]

end

/-! ### Theorem_4_1_3_2 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.1.3.2 lies in the cubic-regularization least-Hessian-eigenvalue domain.

Sampled owner declarations:
* `RelaxedRegularizedNewtonIteration` in `Definition_4_1_5`, the chapter owner for the iterate
  sequence, regularization schedule, and update law;
* `hessianLeastEigenvalue` and `cubicRegularizationDelta` in `Definition_4_1_6`, the owners for
  `λ_min(∇² f x)` and the decrement `δ_k`;
* `RelaxedRegularizedNewtonIteration.HasCubicRegularizationHypotheses` in `Theorem_4_1_3_1`,
  the shared theorem-family owner for the one-step least-eigenvalue comparisons, the decrement
  bootstrap assumptions, and the cubic-model estimates;
* `tsum_cubicRegularization_delta_seq_le_one_sub_initial` in `Theorem_4_1_3_1`, the upstream
  summability consequence reused by the present bound.

Best owner abstraction:
* source-facing: the uniform lower and upper bounds on `λ_min(∇² f (x_k))` along a relaxed
  cubic-regularization trajectory;
* core/canonical: `RelaxedRegularizedNewtonIteration`, `λ_min(∇² f x)`,
  `cubicRegularizationDelta`, and the shared hypothesis owner from `Theorem_4_1_3_1`;
* bridge/view: the local decrement notation `δ` attached to a fixed trajectory.

Primitive data:
* the objective `f`,
* the relaxed regularized Newton trajectory `method`,
* the shared hypothesis owner from Theorem 4.1.3.1.

Derived API:
* the exponential lower and upper bounds for `λ_min(∇² f (method k))`.
-/

section

open RelaxedRegularizedNewtonIteration

variable (L : ℝ) (f : E → ℝ) {stepMap : ℝ → E → E}
variable (method : RelaxedRegularizedNewtonIteration stepMap L)

local notation "δ" => fun k : ℕ ↦ cubicRegularizationDelta f (method k) L

-- Proof sketch: combine `hmethod.lambda_succ` and `hmethod.lambda_succ_upper` with the step
-- estimate to obtain
-- `λ_min(∇² f (x_{i+1})) ∈ [(1 - δ_i) λ_min(∇² f (x_i)), (1 + δ_i) λ_min(∇² f (x_i))]`.
-- The lower bound then comes from summing `log (1 - δ_i)`, while the upper bound comes from
-- summing `log (1 + δ_i)`. In both directions the controlling series estimate is supplied by the
-- theorem-family API from `Theorem_4_1_3_1`.
/-- Helper for Theorem 4.1.3.2: the one-step upper Hessian comparison rewrites into the
multiplicative estimate `λ_{k+1} ≤ (1 + δ_k) λ_k`. -/
lemma cubicRegularization_lambda_succ_le_one_add_delta_mul
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (k : ℕ) :
    λ_min(∇²f(method (k + 1))) ≤
      (1 + δ k) * λ_min(∇²f(method k)) := by
  have hL : 0 < L := method.L_pos
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hLambda_k :=
    cubicRegularization_hessianLeastEigenvalue_pos
      (L := L) (f := f) (method := method) hrec k
  have hstep :=
    cubicRegularization_step_norm_le_lambda_mul_delta
      (L := L) (f := f) (method := method) hrec k hLambda_k
  have hmul :
      L * ‖method (k + 1) - method k‖ ≤
        λ_min(∇²f(method k)) * δ k := by
    -- Rewrite the step-length estimate into the decrement form used by the source proof.
    calc
      L * ‖method (k + 1) - method k‖
          ≤ L * ((λ_min(∇²f(method k)) / L) * δ k) := by
        exact mul_le_mul_of_nonneg_left hstep hL.le
      _ = λ_min(∇²f(method k)) * δ k := by
        field_simp [hL.ne']
  -- Substitute the step-length control into the upper Hessian Lipschitz comparison.
  calc
    λ_min(∇²f(method (k + 1)))
        ≤ λ_min(∇²f(method k)) + L * ‖method (k + 1) - method k‖ :=
      hmethod.lambda_succ_upper k
    _ ≤ λ_min(∇²f(method k)) + λ_min(∇²f(method k)) * δ k := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hmul (λ_min(∇²f(method k)))
    _ = (1 + δ k) * λ_min(∇²f(method k)) := by
      ring

/-- Helper for Theorem 4.1.3.2: iterating the one-step multiplicative bounds sandwiches the least
Hessian eigenvalue between the corresponding finite products. -/
lemma cubicRegularization_hessianLeastEigenvalue_between_partial_products
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (k : ℕ) :
    (((Finset.prod (Finset.range k) fun i ↦ 1 - δ i) * λ_min(∇²f(method 0))) ≤
        λ_min(∇²f(method k))) ∧
      (λ_min(∇²f(method k)) ≤
        (Finset.prod (Finset.range k) fun i ↦ 1 + δ i) * λ_min(∇²f(method 0))) := by
  induction k with
  | zero =>
      -- At the initial index both finite products are empty, so the bounds are exact.
      simp
  | succ k ih =>
      rcases ih with ⟨hlower, hupper⟩
      have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
      have hLambda_k :=
        cubicRegularization_hessianLeastEigenvalue_pos
          (L := L) (f := f) (method := method) hrec k
      have hd_nonneg :
          0 ≤ δ k :=
        cubicRegularizationDelta_nonneg
          (L := L) (f := f) (x := method k) method.L_pos.le
      have hone_sub_nonneg : 0 ≤ 1 - δ k := by
        have hδk :=
          (cubicRegularization_bootstrap_invariant
            (L := L) (f := f) (method := method) hrec k).2
        linarith
      have hone_add_nonneg : 0 ≤ 1 + δ k := by
        linarith
      have hstep_lower :=
        cubicRegularization_lambda_succ_ge_one_sub_delta_mul
          (L := L) (f := f) (method := method) hrec k hLambda_k
      have hstep_upper :=
        cubicRegularization_lambda_succ_le_one_add_delta_mul
          (L := L) (f := f) (method := method) hmethod k
      constructor
      · -- Multiply the inductive lower bound by `1 - δ_k` and then apply the next-step estimate.
        calc
          (Finset.prod (Finset.range (k + 1)) fun i ↦ 1 - δ i) * λ_min(∇²f(method 0))
              = (1 - δ k) * ((Finset.prod (Finset.range k) fun i ↦ 1 - δ i) *
                  λ_min(∇²f(method 0))) := by
            rw [Finset.prod_range_succ]
            ring
          _ ≤ (1 - δ k) * λ_min(∇²f(method k)) := by
            exact mul_le_mul_of_nonneg_left hlower hone_sub_nonneg
          _ ≤ λ_min(∇²f(method (k + 1))) :=
            hstep_lower
      · -- Multiply the inductive upper bound by `1 + δ_k` and absorb the one-step upper estimate.
        calc
          λ_min(∇²f(method (k + 1)))
              ≤ (1 + δ k) * λ_min(∇²f(method k)) :=
            hstep_upper
          _ ≤ (1 + δ k) * ((Finset.prod (Finset.range k) fun i ↦ 1 + δ i) *
                λ_min(∇²f(method 0))) := by
            exact mul_le_mul_of_nonneg_left hupper hone_add_nonneg
          _ = (Finset.prod (Finset.range (k + 1)) fun i ↦ 1 + δ i) *
                λ_min(∇²f(method 0)) := by
            rw [Finset.prod_range_succ]
            ring

/-- Helper for Theorem 4.1.3.2: the geometric majorant from Theorem 4.1.3.1 gives the sharper
total decrement estimate `∑ δ_k ≤ 3 / 4`. -/
lemma tsum_cubicRegularization_delta_seq_le_three_quarters
    (hmethod : method.HasCubicRegularizationHypotheses f) :
    (∑' k, δ k) ≤ (3 / 4 : ℝ) := by
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hgeom : Summable (fun k : ℕ ↦ (2 / 3 : ℝ) ^ k) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hmajor :
      Summable (fun k : ℕ ↦ δ 0 * (2 / 3 : ℝ) ^ k) :=
    hgeom.mul_left _
  have hsum_le :
      (∑' k, δ k) ≤ ∑' k, δ 0 * (2 / 3 : ℝ) ^ k := by
    exact (cubicRegularization_delta_seq_summable
      (L := L) (f := f) (method := method) hrec).tsum_le_tsum
        (fun k ↦ cubicRegularization_delta_le_initial_mul_two_thirds_pow
          (L := L) (f := f) (method := method) hrec k)
        hmajor
  have hmajor_tsum :
      (∑' k, δ 0 * (2 / 3 : ℝ) ^ k) = δ 0 * 3 := by
    rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num)]
    norm_num
  -- Evaluate the geometric series and use the bootstrap bound on `δ₀`.
  calc
    (∑' k, δ k) ≤ ∑' k, δ 0 * (2 / 3 : ℝ) ^ k :=
      hsum_le
    _ = δ 0 * 3 := hmajor_tsum
    _ ≤ (3 / 4 : ℝ) := by
      nlinarith [hmethod.delta0_le_quarter]

/-- Helper for Theorem 4.1.3.2: every finite upper product is bounded by `exp (3 / 4)` via
`∏ (1 + δ_i) ≤ exp (∑ δ_i)`. -/
lemma cubicRegularization_partialProduct_one_add_le_exp_three_quarters
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (k : ℕ) :
    (Finset.prod (Finset.range k) fun i ↦ 1 + δ i) ≤ Real.exp (3 / 4 : ℝ) := by
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hsum_le_tsum :
      Finset.sum (Finset.range k) (fun i ↦ δ i) ≤ ∑' i, δ i := by
    exact (cubicRegularization_delta_seq_summable
      (L := L) (f := f) (method := method) hrec).sum_le_tsum
        (Finset.range k)
        (fun i _ ↦ cubicRegularizationDelta_nonneg
          (L := L) (f := f) (x := method i) method.L_pos.le)
  -- Compare the finite product with the exponential of the finite sum and then with the total sum.
  calc
    Finset.prod (Finset.range k) (fun i ↦ 1 + δ i)
        ≤ Real.exp (Finset.sum (Finset.range k) fun i ↦ δ i) := by
      exact Real.prod_one_add_le_exp_sum _ (fun i ↦
        cubicRegularizationDelta_nonneg
          (L := L) (f := f) (x := method i) method.L_pos.le)
    _ ≤ Real.exp (∑' i, δ i) := by
      exact Real.exp_le_exp_of_le hsum_le_tsum
    _ ≤ Real.exp (3 / 4 : ℝ) := by
      exact Real.exp_le_exp_of_le <|
        tsum_cubicRegularization_delta_seq_le_three_quarters
          (L := L) (f := f) (method := method) hmethod

/-- Helper for Theorem 4.1.3.2: every finite lower product stays above `exp (-1)` once the
bootstrap bound `δ_i ≤ 1 / 4` is combined with the logarithmic estimate
`1 - (1 - δ_i)⁻¹ ≤ log (1 - δ_i)`. -/
lemma cubicRegularization_exp_neg_one_le_partialProduct_one_sub
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (k : ℕ) :
    Real.exp (-1 : ℝ) ≤ (Finset.prod (Finset.range k) fun i ↦ 1 - δ i) := by
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hsum_le_tsum :
      Finset.sum (Finset.range k) (fun i ↦ δ i) ≤ ∑' i, δ i := by
    exact (cubicRegularization_delta_seq_summable
      (L := L) (f := f) (method := method) hrec).sum_le_tsum
        (Finset.range k)
        (fun i _ ↦ cubicRegularizationDelta_nonneg
          (L := L) (f := f) (x := method i) method.L_pos.le)
  have hone_sub_pos (i : ℕ) : 0 < 1 - δ i := by
    have hδi :=
      (cubicRegularization_bootstrap_invariant
        (L := L) (f := f) (method := method) hrec i).2
    linarith
  have hratio_bound (i : ℕ) :
      δ i / (1 - δ i) ≤ (4 / 3 : ℝ) * δ i := by
    have hd_nonneg :
        0 ≤ δ i :=
      cubicRegularizationDelta_nonneg
        (L := L) (f := f) (x := method i) method.L_pos.le
    have hδi :=
      (cubicRegularization_bootstrap_invariant
        (L := L) (f := f) (method := method) hrec i).2
    have hdenom_ge : (3 / 4 : ℝ) ≤ 1 - δ i := by
      linarith
    have hinv_le : (1 - δ i)⁻¹ ≤ (4 / 3 : ℝ) := by
      have hthree_fourths_pos : 0 < (3 / 4 : ℝ) := by
        norm_num
      simpa [one_div] using
        (one_div_le_one_div_of_le hthree_fourths_pos hdenom_ge)
    -- The bootstrap interval turns the reciprocal factor into the uniform constant `4 / 3`.
    calc
      δ i / (1 - δ i) = δ i * (1 - δ i)⁻¹ := by
        rw [div_eq_mul_inv]
      _ ≤ δ i * (4 / 3 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hinv_le hd_nonneg
      _ = (4 / 3 : ℝ) * δ i := by
        ring
  have hsum_ratio_le_one :
      Finset.sum (Finset.range k) (fun i ↦ δ i / (1 - δ i)) ≤ (1 : ℝ) := by
    calc
      Finset.sum (Finset.range k) (fun i ↦ δ i / (1 - δ i))
          ≤ Finset.sum (Finset.range k) (fun i ↦ (4 / 3 : ℝ) * δ i) := by
        exact Finset.sum_le_sum (fun i _ ↦ hratio_bound i)
      _ = (4 / 3 : ℝ) * Finset.sum (Finset.range k) (fun i ↦ δ i) := by
        rw [Finset.mul_sum]
      _ ≤ (4 / 3 : ℝ) * ∑' i, δ i := by
        exact mul_le_mul_of_nonneg_left hsum_le_tsum (by norm_num)
      _ ≤ (4 / 3 : ℝ) * (3 / 4 : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (tsum_cubicRegularization_delta_seq_le_three_quarters
            (L := L) (f := f) (method := method) hmethod)
          (by norm_num)
      _ = 1 := by
        norm_num
  have hsum_log_lower :
      -(Finset.sum (Finset.range k) fun i ↦ δ i / (1 - δ i))
        ≤ Finset.sum (Finset.range k) (fun i ↦ Real.log (1 - δ i)) := by
    -- Sum the pointwise logarithmic lower bounds coming from `1 - x⁻¹ ≤ log x`.
    have hsum_neg_le :
        Finset.sum (Finset.range k) (fun i ↦ -(δ i / (1 - δ i)))
          ≤ Finset.sum (Finset.range k) (fun i ↦ Real.log (1 - δ i)) := by
      exact Finset.sum_le_sum (fun i _ ↦ by
        have hterm : -(δ i / (1 - δ i)) ≤ Real.log (1 - δ i) := by
          have hlog :=
            Real.one_sub_inv_le_log_of_pos (hone_sub_pos i)
          have hrewrite :
              1 - (1 - δ i)⁻¹ = -(δ i / (1 - δ i)) := by
            have hne : 1 - δ i ≠ 0 := (hone_sub_pos i).ne'
            field_simp [hne]
            ring
          exact hrewrite ▸ hlog
        exact hterm)
    simpa [Finset.sum_neg_distrib] using hsum_neg_le
  have hprod_pos : 0 < Finset.prod (Finset.range k) (fun i ↦ 1 - δ i) := by
    exact Finset.prod_pos (fun i _ ↦ hone_sub_pos i)
  have hlog_prod_lower :
      -1 ≤ Real.log (Finset.prod (Finset.range k) fun i ↦ 1 - δ i) := by
    calc
      -1 ≤ -(Finset.sum (Finset.range k) fun i ↦ δ i / (1 - δ i)) := by
        nlinarith [hsum_ratio_le_one]
      _ ≤ Finset.sum (Finset.range k) (fun i ↦ Real.log (1 - δ i)) :=
        hsum_log_lower
      _ = Real.log (Finset.prod (Finset.range k) fun i ↦ 1 - δ i) := by
        symm
        exact Real.log_prod (fun i hi ↦ (hone_sub_pos i).ne')
  -- Exponentiate the logarithmic lower bound to recover the scalar product estimate.
  calc
    Real.exp (-1 : ℝ) ≤
        Real.exp (Real.log (Finset.prod (Finset.range k) fun i ↦ 1 - δ i)) := by
      exact Real.exp_le_exp_of_le hlog_prod_lower
    _ = Finset.prod (Finset.range k) (fun i ↦ 1 - δ i) := by
      rw [Real.exp_log hprod_pos]

/-- Theorem 4.1.3.2: under the stronger theorem-family hypotheses
`method.HasCubicRegularizationHypotheses f` extending the recurrence assumptions from
Theorem 4.1.3.1, the least Hessian eigenvalue along the relaxed cubic-regularization iterates
stays between `e⁻¹` and `e^(3/4)` times its initial value. -/
theorem cubicRegularization_hessianLeastEigenvalue_bounds
    (hmethod : method.HasCubicRegularizationHypotheses f) (k : ℕ) :
    Real.exp (-1 : ℝ) * λ_min(∇² f (method 0)) ≤ λ_min(∇² f (method k)) ∧
      λ_min(∇² f (method k)) ≤ Real.exp (3 / 4 : ℝ) * λ_min(∇² f (method 0)) := by
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hLambda0 :=
    cubicRegularization_hessianLeastEigenvalue_pos
      (L := L) (f := f) (method := method) hrec 0
  rcases cubicRegularization_hessianLeastEigenvalue_between_partial_products
      (L := L) (f := f) (method := method) hmethod k with
    ⟨hlower, hupper⟩
  constructor
  · -- Control the lower product by `exp (-1)` and then transport it to the least eigenvalue.
    calc
      Real.exp (-1 : ℝ) * λ_min(∇²f(method 0))
          ≤ (Finset.prod (Finset.range k) fun i ↦ 1 - δ i) * λ_min(∇²f(method 0)) := by
        exact mul_le_mul_of_nonneg_right
          (cubicRegularization_exp_neg_one_le_partialProduct_one_sub
            (L := L) (f := f) (method := method) hmethod k)
          hLambda0.le
      _ ≤ λ_min(∇²f(method k)) :=
        hlower
  · -- Control the upper product by `exp (3 / 4)` and then transport it to the least eigenvalue.
    calc
      λ_min(∇²f(method k))
          ≤ (Finset.prod (Finset.range k) fun i ↦ 1 + δ i) * λ_min(∇²f(method 0)) :=
        hupper
      _ ≤ Real.exp (3 / 4 : ℝ) * λ_min(∇²f(method 0)) := by
        exact mul_le_mul_of_nonneg_right
          (cubicRegularization_partialProduct_one_add_le_exp_three_quarters
            (L := L) (f := f) (method := method) hmethod k)
          hLambda0.le

end

/-! ### Theorem_4_1_3_3 (from Chap04) -/
open Filter
open scoped Gradient Topology

noncomputable section

universe u

/- Theorem 4.1.3.3 lies in the cubic-regularization Newton asymptotic domain.

Sampled owner declarations:
* `RelaxedRegularizedNewtonIteration.HasCubicRegularizationRecurrenceHypotheses` in
  `Theorem_4_1_3_1`, the chapter owner for the primitive cubic-regularization recurrence data;
* `RelaxedRegularizedNewtonIteration.HasCubicRegularizationHypotheses` in
  `Theorem_4_1_3_1`, the strengthened theorem-family owner used only when the symmetric upper
  least-Hessian-eigenvalue comparison is genuinely needed;
* `cubicRegularizationDelta` and `hessianLeastEigenvalue` in `Definition_4_1_6`, the owners for
  the decrement `δ_k` and the least Hessian eigenvalue `λ_min(∇² f (x_k))`;
* `cubicRegularization_hessianLeastEigenvalue_bounds` in `Theorem_4_1_3_2`, the upstream chapter
  theorem whose exact lower-and-upper spectral bound shape is reused here;
* `hessian_isSelfAdjoint_of_contDiffAt` in `Text_4_2_3`, the project owner that supplies the
  pointwise Hessian-symmetry bridge needed to turn strict positivity of `λ_min(∇² f x)` into the
  canonical operator-positivity owner at a limit point;
* `strict_local_minimizer_of_gradient_zero_of_hessian_lower_bound` in `Theorem_1_4_21`, the
  intrinsic second-order sufficient-condition owner used to pass from the limit Hessian
  positivity statement to the local-minimum conclusion;
* `HasEventuallySuperlinearErrorBound` in `Chap01/Definition_1_2_7`, the project owner for
  quadratic scalar recurrences, sampled to verify that the double-exponential estimate below is a
  genuine source-facing specialization rather than a duplicate owner alias.

Best owner abstraction:
* source-facing: asymptotic consequences for a relaxed cubic-regularization Newton trajectory;
* core/canonical: `RelaxedRegularizedNewtonIteration`,
  `method.HasCubicRegularizationRecurrenceHypotheses f`,
  `cubicRegularizationDelta`, and `λ_min(∇² f x)`;
* bridge/view: the local notation `δ` for the canonical decrement sequence along a fixed
  trajectory.

Primitive data:
* the objective `f`,
* the relaxed Newton trajectory `method`,
* the chapter owner `method.HasCubicRegularizationRecurrenceHypotheses f` for the recurrence
  consequences,
* the stronger owner `method.HasCubicRegularizationHypotheses f` only for the trajectory bounds
  that reuse `Theorem_4_1_3_2`,
* the pointwise `C²` regularity bridge at that limit point.

Derived API:
* Cauchy convergence of the iterates,
* existence and uniqueness of the feasible limit point from the trajectory Cauchy theorem plus the
  canonical completeness API for closed subsets,
* the double-exponential decrement bound,
* continuity of `x ↦ λ_min(∇² f x)` and of `∇ f` at a `C²` limit point,
* strict positivity of the limit least Hessian spectral value together with positivity of the
  intrinsic Hessian operator after the canonical symmetry bridge,
* stationarity of the limit point from the double-exponential gradient decay and the trajectory
  limit,
* the local-minimum consequence,
* the corresponding double-exponential gradient bound.

This file therefore reuses the chapter owner
`RelaxedRegularizedNewtonIteration.HasCubicRegularizationRecurrenceHypotheses` for the
double-exponential decrement estimate, and only invokes the stronger owner
`RelaxedRegularizedNewtonIteration.HasCubicRegularizationHypotheses` when the spectral envelope
from `Theorem_4_1_3_2` is genuinely required. In the local-optimality layer it reuses the
pointwise Hessian-symmetry owner from `Text_4_2_3` together with the intrinsic Hessian owner
`hessian f x`, using the Chapter 1 second-order sufficient-condition theorem only through its
intrinsic lower-bound form, rather than introducing a parallel local matrix-symmetry wrapper. The
continuity of `x ↦ λ_min(∇² f x)` and the stationary limit-point condition are treated as derived
consequences of the `C²` hypothesis together with the trajectory convergence and gradient decay,
not as primitive public inputs.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Trajectory

open RelaxedRegularizedNewtonIteration

variable (L : ℝ) (f : E → ℝ) {stepMap : ℝ → E → E}
variable (method : RelaxedRegularizedNewtonIteration stepMap L)
variable (hmethod : method.HasCubicRegularizationHypotheses f)

local notation "δ" => fun k : ℕ ↦ cubicRegularizationDelta f (method k) L

-- Proof sketch: use the step bound together with the uniform least-eigenvalue upper estimate to
-- compare `‖x_{k+1} - x_k‖` with a constant multiple of `δ k`. Since `δ` is summable, the
-- increment norms are summable as well, hence `method` is Cauchy.
/-- Theorem 4.1.3.3 (1): under the recursion hypotheses from the preceding cubic-regularization
Newton theorems, the iterate sequence is Cauchy. -/
theorem cubicRegularizationNewton_iterates_cauchy
    (hmethod : method.HasCubicRegularizationHypotheses f)
    :
    CauchySeq method :=
  by
  let C : ℝ := (Real.exp (3 / 4 : ℝ) * λ_min(∇² f (method 0))) / L
  have hL : 0 < L := method.L_pos
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hdist :
      ∀ k : ℕ, dist (method k) (method (k + 1)) ≤ C * δ k := by
    intro k
    have hLambda_k :=
      cubicRegularization_hessianLeastEigenvalue_pos
        (L := L) (f := f) (method := method) hrec k
    have hstep :=
      cubicRegularization_step_norm_le_lambda_mul_delta
        (L := L) (f := f) (method := method) hrec k hLambda_k
    have hd_nonneg :
        0 ≤ δ k :=
      cubicRegularizationDelta_nonneg
        (L := L) (f := f) (x := method k) hL.le
    rcases cubicRegularization_hessianLeastEigenvalue_bounds
        (L := L) (f := f) (method := method) hmethod k with
      ⟨_, hupper⟩
    have hratio :
        λ_min(∇² f (method k)) / L ≤
          (Real.exp (3 / 4 : ℝ) * λ_min(∇² f (method 0))) / L := by
      exact div_le_div_of_nonneg_right hupper hL.le
    -- Compare each increment with a fixed multiple of the summable decrement sequence.
    calc
      dist (method k) (method (k + 1)) = ‖method (k + 1) - method k‖ := by
        rw [dist_eq_norm]
        simpa using norm_sub_rev (method k) (method (k + 1))
      _ ≤ (λ_min(∇² f (method k)) / L) * δ k :=
        hstep
      _ ≤ ((Real.exp (3 / 4 : ℝ) * λ_min(∇² f (method 0))) / L) * δ k := by
        exact mul_le_mul_of_nonneg_right hratio hd_nonneg
      _ = C * δ k := by
        rfl
  have hsummable :
      Summable (fun k : ℕ ↦ C * δ k) :=
    (cubicRegularization_delta_seq_summable
      (L := L) (f := f) (method := method) hrec).mul_left C
  exact cauchySeq_of_dist_le_of_summable
    (fun k : ℕ ↦ C * δ k) hdist hsummable

-- Proof sketch: first apply `cubicRegularizationNewton_iterates_cauchy hmethod`, then use the
-- canonical convergence theorem `cauchySeq_tendsto_of_isComplete` for the closed feasible set
-- `ℱ`. Hausdorff uniqueness of limits supplies uniqueness of the feasible limit point.
/-- Theorem 4.1.3.3 (2): a relaxed cubic-regularization Newton trajectory contained in a closed
feasible set converges to a unique feasible limit point. -/
theorem cubicRegularizationNewton_iterates_tendsto_unique_feasible_limit
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (ℱ : Set E)
    (hx_mem : ∀ k, method k ∈ ℱ)
    (hF_closed : IsClosed ℱ) :
    ∃! xStar, xStar ∈ ℱ ∧ Tendsto method atTop (𝓝 xStar) :=
  by
  have hcauchy :=
    cubicRegularizationNewton_iterates_cauchy
      (L := L) (f := f) (method := method) hmethod
  rcases cauchySeq_tendsto_of_isComplete hF_closed.isComplete hx_mem hcauchy with
    ⟨xStar, hxStar_mem, hxtendsto⟩
  refine ⟨xStar, ⟨hxStar_mem, hxtendsto⟩, ?_⟩
  intro y hy
  rcases hy with ⟨hy_mem, hytendsto⟩
  -- The feasible limit is unique because the ambient finite-dimensional space is Hausdorff.
  have hy_eq : y = xStar :=
    tendsto_nhds_unique hytendsto hxtendsto
  simpa [hy_eq]

-- Proof sketch: rescale `δ k` by `16 / 9`, use the recursive bound
-- `δ_{k+1} ≤ (3 / 2) (δ_k / (1 - δ_k))^2`, and exploit `δ 0 ≤ 1 / 4` to show the rescaled
-- sequence squares at each step and starts below `1 / 2`. Iterating yields the
-- double-exponential estimate.
/-- The canonical cubic-regularization decrement sequence along a relaxed Newton trajectory admits
the textbook double-exponential bound once the quadratic recurrence and the smallness condition
`δ₀ ≤ 1 / 4` hold. -/
theorem cubicRegularizationNewton_delta_le_double_exponential
    (hrec : method.HasCubicRegularizationRecurrenceHypotheses f) (k : ℕ) :
    δ k ≤ (9 / 16 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ k) :=
  by
  -- TODO: prove the exact rescaled recurrence `hatδ_{k+1} ≤ hatδ_k²` and iterate it.
  sorry

-- Proof sketch: combine the canonical identity
-- `δ k = L * ‖∇ f(method k)‖ / λ_min(∇² f(method k))^2` with the double-exponential bound for
-- `δ k` and the uniform least-eigenvalue upper estimate along the trajectory.
/-- For every `k`, the gradients along the cubic-regularization Newton iterates satisfy the
textbook double-exponential estimate. -/
theorem cubicRegularizationNewton_gradient_norm_le_double_exponential
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (k : ℕ) :
    ‖∇ f (method k)‖ ≤
      (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
        ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ k) :=
  by
  -- TODO: combine the decrement identity with the upper spectral envelope and the previous theorem.
  sorry

end Trajectory

section LocalOptimality

open RelaxedRegularizedNewtonIteration

variable (L : ℝ) (f : E → ℝ) {stepMap : ℝ → E → E}
variable (method : RelaxedRegularizedNewtonIteration stepMap L)
variable (hmethod : method.HasCubicRegularizationHypotheses f)

/-- Helper for Theorem 4.1.3.3: the uniform spectral lower bound along a convergent
cubic-regularization Newton trajectory passes to a quadratic lower bound for the limit Hessian. -/
lemma cubicRegularizationNewton_limit_hessian_quadratic_lower_bound
    (hmethod : method.HasCubicRegularizationHypotheses f)
    {xStar : E} (hxtendsto : Tendsto method atTop (𝓝 xStar))
    (hcontDiff : ContDiffAt ℝ 2 f xStar) :
    ∃ μ > 0, ∀ h : E, μ * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar h) h := by
  -- TODO: transport the uniform lower spectral bound to the limit Hessian through a local `C²`
  -- neighborhood and fixed unit directions.
  sorry

-- Proof sketch: combine the uniform lower eigenvalue bound with convergence of `method` and the
-- continuity of `x ↦ λ_min(∇² f x)` derived from `ContDiffAt ℝ 2 f xStar` to deduce
-- `0 < λ_min(∇²f xStar)`.
/-- A limit point of the cubic-regularization Newton trajectory inherits a strictly positive least
Hessian spectral value from the uniform lower least-eigenvalue bound along the trajectory. -/
theorem cubicRegularizationNewton_limit_hessianLeastEigenvalue_pos
    (hmethod : method.HasCubicRegularizationHypotheses f)
    {xStar : E} (hxtendsto : Tendsto method atTop (𝓝 xStar))
    (hcontDiff : ContDiffAt ℝ 2 f xStar) :
    0 < λ_min(∇²f xStar) :=
  by
  -- TODO: deduce positivity of the least spectral value from the quadratic lower bound helper.
  sorry

-- Proof sketch: combine the strict positivity of `λ_min(∇²f xStar)` from
-- `cubicRegularizationNewton_limit_hessianLeastEigenvalue_pos` with Hessian self-adjointness from
-- `hessian_isSelfAdjoint_of_contDiffAt`; for a self-adjoint operator, positivity of the least
-- spectral value gives positivity in the canonical operator sense.
/-- A `C²` limit point of the cubic-regularization Newton trajectory has positive intrinsic
Hessian operator. -/
theorem cubicRegularizationNewton_limit_hessian_isPositive
    (hmethod : method.HasCubicRegularizationHypotheses f)
    {xStar : E} (hxtendsto : Tendsto method atTop (𝓝 xStar))
    (hcontDiff : ContDiffAt ℝ 2 f xStar) :
    (hessian f xStar).IsPositive :=
  by
  -- TODO: combine the quadratic lower bound helper with Hessian self-adjointness.
  sorry

-- Proof sketch: use `ContDiffAt ℝ 2 f xStar` to derive differentiability and continuity of
-- `∇ f` at `xStar`. The double-exponential gradient bound shows `∇ f (method k) → 0`, and
-- `hxtendsto` then forces `HasGradientAt f 0 xStar`. Combine this with the intrinsic
-- limit-Hessian positivity statement from `cubicRegularizationNewton_limit_hessian_isPositive`,
-- then apply the intrinsic second-order sufficient-condition theorem
-- `strict_local_minimizer_of_gradient_zero_of_hessian_lower_bound`, and finally forget
-- strictness to a local minimum.
/-- A limit point of a relaxed cubic-regularization Newton trajectory is a local minimum once `f`
is `C²` there; the stationarity and least-Hessian-eigenvalue continuity hypotheses are derived
internally from the trajectory convergence and the chapter's gradient-decay estimate. -/
theorem cubicRegularizationNewton_limit_isLocalMin
    (hmethod : method.HasCubicRegularizationHypotheses f)
    {xStar : E}
    (hxtendsto : Tendsto method atTop (𝓝 xStar))
    (hcontDiff : ContDiffAt ℝ 2 f xStar) :
    IsLocalMin f xStar :=
  by
  -- TODO: combine gradient decay with continuity of `∇ f` and the quadratic lower bound helper.
  sorry

end LocalOptimality
