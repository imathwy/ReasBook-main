import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_21
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open scoped NewtonDecrement
open scoped SelfConcordantAuxiliaryFunction

/- Proposition 5.2.2 lies in the Chapter 5 self-concordant two-stage-strategy domain.

Sampled owner declarations:
* `DampedNewton.Method.IsSelfConcordant` in `Definition_5_2_1`, the Chapter 5 refinement of the
  recursive damped Newton owner;
* `NewtonDecrement.ofDetNeZero` and the source-facing notation
  `ndec(f, x, Mf, hx, hH)` in `Definition_5_0_24`, the canonical Newton-decrement owner at a
  domain point with nondegenerate Hessian;
* `selfConcordantTwoStageStrategy` and `selfConcordantTwoStageStrategy_eq_damped_iff` in
  `Definition_5_2_2`, the source-facing two-stage owner and its threshold bridge;
* `IsMinOn` in mathlib, the canonical minimizer owner reused throughout Chapter 5.

Best owner abstraction:
* source-facing: the assertion that the first `N` iterates of the damped Newton method remain in
  Stage 1 of the two-stage strategy;
* core/canonical: `DampedNewton.Method.IsSelfConcordant`, `ndec(f, x, Mf, hx, hH)`,
  `selfConcordantTwoStageStrategy`, and `IsMinOn f dom xStar`;
* bridge/view: the threshold inequality
  `1 / (2 M_f) ≤ NewtonDecrement.ofDetNeZero ...`.

Primitive data:
* the damped self-concordant Newton method;
* the objective `f` and domain `dom`;
* the positive self-concordance parameter `Mf`;
* the canonical Newton decrement at each iterate, read through the chapter notation
  `ndec(f, method k, Mf, hmethod.iterates_mem k, method.hessian_nondegenerate k)`;
* the Stage-1 membership condition for the first `N` iterates;
* the canonical minimizer owner `IsMinOn f dom xStar`.

Derived API:
* the pointwise threshold characterization of Stage 1 from
  `selfConcordantTwoStageStrategy_eq_damped_iff`;
* the lower bound `f xStar ≤ f (method k)` obtained by applying `IsMinOn` to any iterate in `dom`;
* the Stage-1 damped-step decrease estimate obtained at each iterate from the canonical one-step
  damped Newton owner.

This file stays source-facing at the level of the Stage-1 segment length, but removes the parallel
free decrement sequence and instead reads Stage 1 directly from the canonical Newton decrement
along the damped self-concordant Newton method. -/

namespace DampedNewton.Method.IsSelfConcordant

section

variable {dom : Set E} {f : E → ℝ} {Mf : NNRealˣ}
variable [IsSelfConcordantOnWith dom (Mf : NNReal) f]
variable {x0 : E}

-- Proof sketch: record Stage 1 directly through the canonical Newton decrement of the damped
-- method and then use `selfConcordantTwoStageStrategy_eq_damped_iff`.
/-- `method.IsStageOneUpTo N` means that the first `N` iterates of the damped self-concordant
Newton method remain in Stage 1 of the two-stage strategy from Definition 5.2.2. -/
def IsStageOneUpTo
    {method : DampedNewton.Method f x0}
    (hmethod : method.IsSelfConcordant dom (Mf : NNReal) SelfConcordantNewtonVariant.damped)
    (N : ℕ) : Prop :=
  ∀ k : ℕ, k < N →
    selfConcordantTwoStageStrategy Mf
        (ndec(
          f, (method k), (Mf : NNReal), (hmethod.iterates_mem k),
          (method.hessian_nondegenerate k))) =
      .damped

-- Proof sketch: unfold `DampedNewton.Method.IsSelfConcordant.IsStageOneUpTo` and apply
-- `selfConcordantTwoStageStrategy_eq_damped_iff` at each iterate.
/-- Expanding `method.IsStageOneUpTo N` says that every index `k < N` satisfies the Stage 1
threshold inequality `1 / (2 M_f) ≤ λ_f(x_k)` for the canonical Newton decrement of `method`. -/
theorem isStageOneUpTo_iff
    {method : DampedNewton.Method f x0}
    (hmethod : method.IsSelfConcordant dom (Mf : NNReal) SelfConcordantNewtonVariant.damped)
    {N : ℕ} :
    hmethod.IsStageOneUpTo N ↔
      ∀ k : ℕ, k < N →
        1 / (2 * (Mf : ℝ)) ≤
          ndec(
            f, (method k), (Mf : NNReal), (hmethod.iterates_mem k),
            (method.hessian_nondegenerate k)) := by
  constructor
  · intro h k hk
    exact
      (selfConcordantTwoStageStrategy_eq_damped_iff Mf
        (ndec(
          f, (method k), (Mf : NNReal), (hmethod.iterates_mem k),
          (method.hessian_nondegenerate k)))).1
        (h k hk)
  · intro h k hk
    exact
      (selfConcordantTwoStageStrategy_eq_damped_iff Mf
        (ndec(
          f, (method k), (Mf : NNReal), (hmethod.iterates_mem k),
          (method.hessian_nondegenerate k)))).2
        (h k hk)

end

end DampedNewton.Method.IsSelfConcordant

-- Proof sketch: use the Stage 1 hypothesis to justify the uniform decrease estimate
-- `f(x_{k + 1}) ≤ f(x_k) - M_f⁻² ω(M_f λ_f(x_k))` for every `k < N`. The Stage 1 hypothesis gives
-- `1 / 2 ≤ M_f λ_f(x_k)`, so monotonicity of `ω` yields the uniform lower bound
-- `M_f⁻² ω(1 / 2)`. Summing these `N` inequalities gives
-- `f(x_N) ≤ f(x_0) - N * M_f⁻² ω(1 / 2)`. Since `xStar` minimizes `f` on `dom` and the method
-- stays in `dom`, we have `f xStar ≤ f(x_N)`, and rearranging yields the stated estimate.
/-- Proposition 5.2.2: if the first `N` iterates of the damped segment of the two-stage
self-concordant Newton method remain in Stage 1, then
`N ≤ M_f^2 (f(x_0) - f(x_f^*)) / ω(1 / 2)`, where `x_f^*` minimizes `f` on the domain. -/
theorem selfConcordantTwoStage_stageOneLength_le
    {dom : Set E} {f : E → ℝ} {Mf : NNRealˣ} [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    {x0 : E}
    (method : DampedNewton.Method f x0)
    (hmethod : method.IsSelfConcordant dom (Mf : NNReal) SelfConcordantNewtonVariant.damped)
    {xStar : E} {N : ℕ}
    (hmin : IsMinOn f dom xStar)
    (hstage : hmethod.IsStageOneUpTo N) :
    (N : ℝ) ≤
      (Mf : ℝ) ^ (2 : ℕ) * (f x0 - f xStar) /
        selfConcordantOmegaAtOneHalf := sorry

end
