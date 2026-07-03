import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap01.FirstOrderTaylorModel
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_20
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_21
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Gradient HessianDualLocalNorm SelfConcordantAuxiliaryFunction

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom Mf f] [HasPositiveDefiniteHessianOn dom f]

/- Theorem 5.1.12 lies in the Chapter 5 self-concordance / dual-local-norm domain.

Sampled owner declarations:
* `HasPositiveDefiniteHessianOn` from `Definition_5_0_23`, the chapter owner for the
  positive-definite-Hessian regime in which the dual local norm is evaluated from domain
  membership alone;
* `HessianDualLocalNorm.ofPosDefMem` from `Definition_5_0_20`, the canonical domain-level bridge
  to the dual local norm;
* `selfConcordantOmegaArg` and `selfConcordantOmegaStarArg` from `Definition_5_0_21`, the
  canonical Chapter 5 owners of the `ω` and `ω_*` arguments;
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the owner for quantitative
  self-concordance;
* `firstOrderTaylorModelAt` from `Chap01/FirstOrderTaylorModel`, the canonical affine Taylor
  owner against which the remainder is measured.

Source/core/bridge triage:
* source-facing: the lower and upper value bounds expressed by the dual local norm of
  `∇ f y - ∇ f x` at `y`;
* core/canonical: `IsSelfConcordantOnWith dom Mf f`, `HasPositiveDefiniteHessianOn dom f`,
  `HessianDualLocalNorm.ofPosDefMem`, and the Chapter 5 auxiliary-function owners `ω` and `ω_*`;
* bridge/view: the gradient-difference covector
  `(toDual ℝ E) (∇ f y - ∇ f x)` and the affine Taylor remainder
  `f y - firstOrderTaylorModelAt f x y`.

Primitive data:
* `dom`, `Mf`, `f`, the points `x` and `y`;
* domain membership of `x` and `y`;
* positive definiteness of the Hessian on `dom`.

Derived API:
* the gradient-difference covector at `y`;
* the domain-level dual local norm bridge `HessianDualLocalNorm.ofPosDefMem`;
* the lower `ω` and upper `ω_*` remainder terms, expressed through the canonical subtype owners
  `selfConcordantOmegaArg` and `selfConcordantOmegaStarArg`.

This file stays source-facing. The theorem is not a new owner: it is a derived consequence of the
dual-local-norm owner, the canonical first-order Taylor model, and the Chapter 5 auxiliary
function owners. -/

private theorem gradientDifferenceDualLocalNorm_nonneg
    (x y : E) (hy : y ∈ dom) :
    0 ≤
      HessianDualLocalNorm.ofPosDefMem f hy
        ((toDual ℝ E) (∇ f y - ∇ f x)) := by
  simpa [HessianDualLocalNorm.ofPosDefMem] using
    dualLocalNorm_nonneg f y
      (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hy)
      (hessian_isInvertible_of_det_ne_zero
        (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hy))
      ((toDual ℝ E) (∇ f y - ∇ f x))

-- Proof sketch: compare `f y` to the first-order Taylor model at `x`, write the remainder in
-- terms of the gradient-difference covector at `y`, and express the resulting lower and upper
-- self-concordant remainders through the canonical Chapter 5 subtype owners
-- `selfConcordantOmegaArg` and `selfConcordantOmegaStarArg`. The only local helper retained here
-- is the nonnegativity witness needed to build the `ω` argument from the domain-level dual local
-- norm bridge.
/-- Theorem 5.1.12: if `f` is self-concordant on `dom` with constant `M_f`, then the
value at `y` is bounded below by the affine Taylor model at `x` plus the remainder term
`M_f⁻² ω(M_f ‖∇ f(y) - ∇ f(x)‖*_y)`, interpreted as
`(1 / 2) ‖∇ f(y) - ∇ f(x)‖*²_y` when `M_f = 0`. In the same zero-parameter limit, the
upper branch also reduces to the quadratic remainder `(1 / 2) ‖∇ f(y) - ∇ f(x)‖*²_y`;
otherwise, if the dual local norm of the gradient difference at `y` is smaller than `1 / M_f`,
then `f y` is bounded above by the affine model plus
`M_f⁻² ω_*(M_f ‖∇ f(y) - ∇ f(x)‖*_y)`. -/
theorem selfConcordant_value_bounds_of_dualLocalNorm_gradient_sub
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) :
    let δ :=
      HessianDualLocalNorm.ofPosDefMem f hy
        ((toDual ℝ E) (∇ f y - ∇ f x))
    let taylor := firstOrderTaylorModelAt f x y
    let tω := selfConcordantOmegaArg Mf δ
      (neg_one_lt_mf_mul_of_nonneg (gradientDifferenceDualLocalNorm_nonneg x y hy))
    f y ≥
        taylor +
          (if hMf : Mf = 0 then
            δ ^ (2 : ℕ) / 2
          else
            (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω) ∧
      (if hMf : Mf = 0 then
        f y ≤
          taylor +
            δ ^ (2 : ℕ) / 2
      else
        ∀ hδ : δ < 1 / (Mf : ℝ),
          let τω := selfConcordantOmegaStarArg Mf δ (mf_mul_lt_one_of_lt_inv hδ)
          f y ≤
            taylor +
              (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω) := sorry
