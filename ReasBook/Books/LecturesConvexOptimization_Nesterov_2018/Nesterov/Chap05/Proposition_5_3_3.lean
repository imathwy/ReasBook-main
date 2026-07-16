import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Proposition 5.3.3 lies in the Chapter 5 barrier-parameter / local-Hessian-norm domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith.barrier_parameter_bound` in `Definition_5_3_2`, the source
  owner inequality for a `ν`-self-concordant barrier;
* `hessianLocalNorm` and the notation `‖u‖[F; x]` in `Definition_5_1_1`, the chapter owner for
  the Hessian-induced local norm;
* `hessianLocalNorm_def` in `Definition_5_1_1`, the canonical owner expansion;
* `sublevelLogBarrier_hessian_quadraticForm_ge_gradient_sq` in `Theorem_5_1_4`, the earlier
  quadratic-form inequality in the same Chapter 5 differential domain.

Source/core/bridge triage:
* source-facing: the fixed-point barrier inequality at `x`;
* core/canonical: the Hessian local norm `‖u‖[F; x]`;
* bridge/view: `hessianLocalNorm_def` together with `Real.sq_sqrt`, which recovers
  `inner ℝ u (hessian F x u)` from that owner.

Primitive data:
* a function `F`;
* a barrier parameter `ν`;
* a base point `x`.
* pointwise Hessian positivity at `x`.

Derived API:
* the equivalent local-norm-square estimate
  `⟪∇ F(x), u⟫² ≤ ν ‖u‖[F; x]^2`;
* the raw Hessian-quadratic-form presentation, recovered canonically from
  `hessianLocalNorm_def`.

This proposition therefore keeps the source-facing left-hand side from
`IsSelfConcordantBarrierOnWith.barrier_parameter_bound`, but refines the right-hand side to the
chapter owner `‖u‖[F; x]` instead of repeating the quadratic form inline. The pointwise theorem
below is the public bridge, and barrier-owner applications should use it with the Hessian
positivity already supplied by `IsSelfConcordantOnWith.hessian_isPositive`. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: for the forward implication, apply the bound to the scaled direction `t • u`,
-- obtaining a quadratic inequality in `t`; nonpositivity of its discriminant yields
-- `⟪∇ F(x), u⟫² ≤ ν ‖u‖[F; x]^2`. Conversely, from the squared bound, use
-- `2ab ≤ a² + b²` after normalizing by `ν`, or complete the square in
-- `2 * ⟪∇ F(x), u⟫ - ⟪∇² F(x)u, u⟫`, to recover the original inequality. The pointwise
-- positivity hypothesis is essential: without it, `‖u‖[F; x]` can vanish on directions where the
-- Hessian quadratic form is negative, so the squared local-norm bound no longer detects the
-- barrier inequality.
/-- Proposition 5.3.3, pointwise owner form: at a fixed point `x` with positive Hessian,
the barrier inequality `2 ⟪∇ F(x), u⟫ - ⟪∇² F(x)u, u⟫ ≤ ν` for every direction `u` is
equivalent to the quadratic-form bound `⟪∇ F(x), u⟫² ≤ ν ‖u‖[F; x]^2` for every `u`,
written on the canonical Chapter 5 local-norm surface. -/
theorem barrier_parameter_bound_iff_gradient_inner_sq_le
    {F : E → ℝ} {ν : NNReal} {x : E} (hPos : (hessian F x).IsPositive) :
    (∀ u : E,
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)) ↔
      ∀ u : E,
        (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * ‖u‖[F; x] ^ (2 : ℕ) := sorry

end
