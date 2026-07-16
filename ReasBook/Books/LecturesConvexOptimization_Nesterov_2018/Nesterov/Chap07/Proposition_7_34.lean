import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_65
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_66
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Theorem_7_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Asymptotics
open Filter
open scoped Gradient HessianDualLocalNorm

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/- Proposition 7.34 lies in the Chapter 7 barrier-subgradient / relative-scale complexity
domain.

Mandatory domain-style sampling:
- `BarrierSubgradientMethod` in `Algorithm_7_14`, the source-facing owner of the actual Chapter 7
  primal iterates;
- `BarrierSubgradientMethod.positiveIterateGeometricMean_isRelativeScaleDeltaApproximation` in
  `Theorem_7_16`, the canonical owner-level relative-scale approximation theorem for those
  iterates;
- `IsRelativeScaleDeltaApproximation` in `Definition_7_65`, the source-facing approximation
  predicate;
- `Asymptotics.IsSoftBigO` and the notation `=Õ[...]` in `Definition_7_66`, the chapter's
  asymptotic-complexity owner.

Best owner abstraction:
- source-facing: the existence of an accuracy-indexed schedule for an actual
  `BarrierSubgradientMethod`, under the same optimizer and barrier assumptions as Theorem 7.16;
- core/canonical: `BarrierSubgradientMethod.iterateGeometricMean`,
  `IsRelativeScaleDeltaApproximation`, and `f =Õ[size; l] g`;
- bridge/view: the inversion from the explicit Chapter 7 rate `δ_k` to a schedule `N(δ)`.

Primitive data:
- the method owner `method : BarrierSubgradientMethod P₀ F ψ v x₀`;
- the maximizing point `x⋆`;
- the barrier parameter `ν`;
- the Chapter 7 concavity, self-concordance, Hessian-positivity, and dual-norm hypotheses from
  Theorem 7.16.

Derived API:
- the schedule `N`;
- the pointwise relative-scale approximation guarantee at `N δ`, derived from the owner-level
  theorem in `Theorem_7_16`;
- the soft-`O` complexity comparison for `N`.

Source/core/bridge triage:
- source-facing: this proposition's schedule-existence theorem for the actual barrier-subgradient
  method;
- core/canonical: the method-level approximation owner from Theorem 7.16;
- bridge/view: the asymptotic schedule extracted from the explicit rate.

The previous version replaced the source-facing method owner by a bare logarithmic lower-rate
hypothesis on arbitrary positive sequences. That lost the optimizer-supplied upper bound needed by
`IsRelativeScaleDeltaApproximation`, so the public API became semantically too weak. This
refinement keeps Proposition 7.34 on the actual `BarrierSubgradientMethod` / `IsMaxOn` owner
surface from Theorem 7.16 and treats only the schedule inversion as the new bridge content.
-/

namespace BarrierSubgradientMethod

section ApproximationSchedule

variable {P0 : Set E} {F ψ : E → ℝ} {v : NNRealˣ} {x0 : P0}
variable (method : BarrierSubgradientMethod P0 F ψ v x0)

-- Proof sketch: combine the geometric-mean lower bound from Theorem 7.16 with an inversion of
-- the owner-level relative-scale approximation theorem for `method.iterateGeometricMean` with an
-- inversion of the explicit rate `δ_k = barrierSubgradientRelativeAccuracyDelta ν k`. Choosing a
-- schedule `N(δ)` so that `δ_{N(δ)} ≤ δ` yields a relative-`δ` approximation, and solving this
-- condition gives a soft-`O(ν / δ²)` bound for `N(δ)` as `δ ↓ 0`.
/-- Proposition 7.34: for the barrier-subgradient approximation scheme `(7.3.33)` applied to a
concave maximization problem of the form `(7.3.29)`, if the logarithmic rate estimate from
Theorem `7.16` holds for an actual barrier-subgradient run with barrier complexity parameter
`ν > 0`, then there exists an iteration schedule `N(δ)` such that the geometric-mean output after
`N(δ)` steps is a relative-`δ` approximation of `ψ(x⋆)`, and `N(δ)` has soft complexity
`\tilde O(ν / δ²)` as `δ ↓ 0`. -/
theorem exists_relativeScaleDeltaApproximation_schedule
    (xStar : P0) (hoptimal : IsMaxOn ψ P0 xStar)
    (ν : NNReal) (hν : 0 < (ν : ℝ))
    [IsSelfConcordantBarrierOnWith P0 ν F]
    [HasPositiveDefiniteHessianOn P0 F]
    (hψ_concave : ConcaveOn ℝ P0 ψ)
    (hψ_dual_bound :
      ∀ x : P0,
        HessianDualLocalNorm.ofPosDefMem F x.2
            (InnerProductSpace.toDualMap ℝ E (∇ ψ x)) ≤
          ψ x) :
    ∃ N : ℝ → ℕ,
      (∀ ⦃δ : ℝ⦄, 0 < δ →
        IsRelativeScaleDeltaApproximation (ψ xStar) δ
          (method.iterateGeometricMean (N δ))) ∧
        (fun δ ↦ (N δ : ℝ)) =Õ[fun δ ↦ ⌈(ν : ℝ) / δ ^ (2 : ℕ)⌉₊;
          nhdsWithin (0 : ℝ) (Set.Ioi 0)]
          (fun δ ↦ (ν : ℝ) / δ ^ (2 : ℕ)) := sorry

end ApproximationSchedule

end BarrierSubgradientMethod

end
