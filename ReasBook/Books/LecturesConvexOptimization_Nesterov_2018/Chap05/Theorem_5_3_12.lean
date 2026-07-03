import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_20
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_3_5_3
import LecturesConvexOptimization_Nesterov_2018.Chap05.Lemma_5_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open HessianDualLocalNorm
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.3.12 lies in the Chapter 5 auxiliary-central-path / analytic-center / local-dual-norm
domain.

Sampled owner declarations:
* `dualLocalNorm` in `Definition_5_0_20`, the chapter owner for the Hessian-metric dual local
  norm of a covector;
* `HessianDualLocalNorm.ofPosDefMem` in `Definition_5_0_20`, the canonical domain-level bridge
  from positive-definite Hessians to that dual norm;
* `IsMinOn` as recalled in `Definition_5_3_3`, the neighboring chapter owner surface for analytic
  centers;
* `IsCentralPath` in `Definition_5_3_6_1`, the chapter owner for the auxiliary central path;
* `dualLocalNorm_gradient_auxiliaryCentralPath_le_barrierParameter_add_two_sqrt_mul_initial` in
  `Lemma_5_3_3`, the chapter bridge that bounds the iterate gradient norm by the analytic-center
  norm `‖∇ F(y₀)‖*_{x_F^*}`;
* `StoppedIntermediateSelfConcordantNewtonMethod` in `Definition_5_3_5_1`, the source-facing
  owner for the stopped intermediate Newton preprocessing method.

Best owner abstraction:
* source-facing: the stopping estimate for a
  `StoppedIntermediateSelfConcordantNewtonMethod`, stated with the auxiliary central path based at
  `y₀` and the analytic center `x_F^*` of the barrier;
* core/canonical: the stopped-method owner
  `StoppedIntermediateSelfConcordantNewtonMethod F y0 (β + γ)` together with the dual local norm
  bridge `HessianDualLocalNorm.ofPosDefMem F xFStar.2 (toDual ℝ E (∇ F (y0 : E)))`;
* bridge/view: the scalar logarithmic helper obtained by abstracting the dual norm and the
  auxiliary decay profile to scalar data.

Primitive data:
* the stopped intermediate Newton method;
* the auxiliary central path `yStar`;
* the analytic center `xFStar`;
* the discrete auxiliary-path parameters `t`;
* the positive-definite-Hessian owner on `dom`, used to form the dual local norm at `xFStar`;
* the positive complexity parameters `γ` and `β + √ν`;
* the exponential decay estimate for `t`;
* the comparison bound of the iterate decrement by the auxiliary-central-path residual norm.

Derived API:
* the stopping index `method.stopIndex`;
* the ordinary Newton decrement `method.decrement k`;
* the logarithmic stopping bound built from the analytic-center norm `‖∇ F(y₀)‖*_{x_F^*}`.

This file therefore keeps the stopped-method owner, the auxiliary central path, and the
analytic-center hypothesis on the public surface, while demoting only the scalar logarithmic
estimate to a private proof helper. -/

section

variable {dom : Set E} {F : E → ℝ} {ν : NNReal} [IsSelfConcordantBarrierOnWith dom ν F]
variable {y0 : dom} {β γ : ℝ}

-- Proof sketch: use the positivity of `γ` and `β + √ν` so that the exponential decay rate and the
-- logarithmic denominator have their textbook sign, then combine the exponential decay estimate
-- for `t_k` with the bound
-- `λ_F(y_k) ≤ β + t_k (ν + 2 √ν) R` for a scalar reference norm `R`.
-- Since `method` stops when the ordinary Newton decrement drops below `β + γ`, solving the
-- resulting scalar inequality for `k` yields the stated natural-ceiling bound.
/-- Auxiliary scalarized stopping estimate: if an auxiliary path-following scheme satisfies the
generic decrement bound `λ_F(y_k) ≤ β + t_k (ν + 2 √ν) R` and the geometric decay estimate for
`t_k`, then the stopping index is bounded by the corresponding logarithmic expression in `R`. -/
private theorem stopIndex_le_natCeil_of_referenceDualNorm
    (method : StoppedIntermediateSelfConcordantNewtonMethod F y0 (β + γ))
    (t : ℕ → ℝ)
    (referenceDualNorm : ℝ)
    (hγ : 0 < γ)
    (hβsqrt : 0 < β + Real.sqrt (ν : ℝ))
    (ht :
      ∀ k : ℕ,
        t k ≤ Real.exp (-γ * (k : ℝ) / (β + Real.sqrt (ν : ℝ))))
    (hdecrement :
      ∀ k : ℕ,
        method.decrement k ≤
          β + t k * (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) * referenceDualNorm)) :
    method.stopIndex ≤
      ⌈((β + Real.sqrt (ν : ℝ)) / γ) *
          Real.log
            ((((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) * referenceDualNorm) / γ)⌉₊ := sorry

-- Proof sketch: apply the auxiliary-central-path gradient estimate from `Lemma_5_3_3` at the
-- path points `yStar (t k)` and the analytic center `xFStar`, turning the source-facing
-- decrement comparison into the scalar bound required by
-- `stopIndex_le_natCeil_of_referenceDualNorm`. The logarithmic stopping estimate then follows
-- with the analytic-center norm `‖∇ F(y₀)‖*_{x_F^*}` on the theorem surface.
/-- Theorem 5.3.12: let `x_F^*` be an analytic center of a `ν`-self-concordant barrier `F`, and
let `y*(t)` be the auxiliary central path based at `y₀`. If a stopped intermediate Newton method
started at `y₀` has decrement bounded along the iterates by
`β + ‖∇ F(y*(t_k))‖*_{y*(t_k)}` for a nonnegative parameter sequence `t_k` that decays like
`exp (-γ k / (β + √ν))`, then the stopping index is at most
`⌈((β + √ν) / γ) log (((ν + 2 √ν) ‖∇ F(y₀)‖*_{x_F^*}) / γ)⌉₊`, provided `γ > 0` and
`β + √ν > 0`. -/
theorem auxiliaryPathFollowing_stopIndex_le_natCeil_terminationBound
    (method : StoppedIntermediateSelfConcordantNewtonMethod F y0 (β + γ))
    [HasPositiveDefiniteHessianOn dom F]
    (yStar : Set.Ici (0 : ℝ) → dom)
    (xFStar : dom)
    (hxFStar : IsMinOn F dom (xFStar : E))
    (hpath : IsCentralPath dom (-∇ F (y0 : E)) F yStar)
    (t : ℕ → Set.Ici (0 : ℝ))
    (hγ : 0 < γ)
    (hβsqrt : 0 < β + Real.sqrt (ν : ℝ))
    (ht :
      ∀ k : ℕ,
        (t k : ℝ) ≤ Real.exp (-γ * (k : ℝ) / (β + Real.sqrt (ν : ℝ))))
    (hdecrement :
      ∀ k : ℕ,
        method.decrement k ≤
          β + ofPosDefMem F (yStar (t k)).2 (toDual ℝ E (∇ F (yStar (t k) : E)))) :
    method.stopIndex ≤
      ⌈((β + Real.sqrt (ν : ℝ)) / γ) *
          Real.log
            ((((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) *
                ofPosDefMem F xFStar.2 (toDual ℝ E (∇ F (y0 : E)))) / γ)⌉₊ := by
  let referenceDualNorm := ofPosDefMem F xFStar.2 (toDual ℝ E (∇ F (y0 : E)))
  refine
    stopIndex_le_natCeil_of_referenceDualNorm
      method
      (fun k ↦ (t k : ℝ))
      referenceDualNorm
      hγ hβsqrt ht ?_
  intro k
  calc
    method.decrement k ≤
        β + ofPosDefMem F (yStar (t k)).2 (toDual ℝ E (∇ F (yStar (t k) : E))) :=
      hdecrement k
    _ ≤
        β + (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) * referenceDualNorm) * (t k : ℝ) := by
      let hF : IsSelfConcordantBarrierOnWith dom ν F := inferInstance
      gcongr
      simpa [referenceDualNorm] using
        hF.dualLocalNorm_gradient_auxiliaryCentralPath_le_barrierParameter_add_two_sqrt_mul_initial
          y0 yStar xFStar hxFStar hpath (t k)
    _ =
        β +
          (t k : ℝ) *
            (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) * referenceDualNorm) := by
      ring

end

end
