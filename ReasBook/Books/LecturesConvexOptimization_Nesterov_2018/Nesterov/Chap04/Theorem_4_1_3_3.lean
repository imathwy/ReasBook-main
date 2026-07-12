import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap01.Theorem_1_4_21
import LecturesConvexOptimization_Nesterov_2018.Chap04.Text_4_2_3
import LecturesConvexOptimization_Nesterov_2018.Chap04.Theorem_4_1_2
import LecturesConvexOptimization_Nesterov_2018.Chap04.Theorem_4_1_3_2

-- Declarations for this item will be appended below by the statement pipeline.

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
