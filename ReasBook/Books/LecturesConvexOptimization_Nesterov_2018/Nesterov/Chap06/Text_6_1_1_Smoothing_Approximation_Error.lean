import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Module
open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped ConvexAnalysis BInducedNorm

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/- Text 6.1.1 lies in the chapter's Fenchel-smoothing / dual-norm domain.

Relevant sampled declarations in this domain:
- `fenchelSmoothApproximation` in `Chap06/Definition_6_2`, the chapter owner for the quadratically
  regularized Fenchel supremum;
- `fenchelSmoothApproximation_apply` in `Chap06/Definition_6_2`, the owner evaluation theorem;
- `fenchelConjugate` in `Chap06/Definition_6_1`, the canonical dual object feeding the smoothing
  construction;
- `dom` in `Chap03/Definition_3_1_1_2`, the chapter owner for the finite-value domain of an
  `EReal`-valued function.

Best owner abstraction:
- source-facing: the approximation-error bound for `fenchelSmoothApproximation`;
- core/canonical: `fenchelSmoothApproximation`;
- bridge/view: its zero-penalty specialization, which is exactly the unsmoothed Fenchel supremum
  model used in the textbook statement.

Primitive data:
- `B : BilinForm ℝ E` with positive-definiteness;
- `f : E → EReal`;
- the smoothing parameter `μ`, the radius bound `L`, and the dual-domain bound `hdual`.

Derived API:
- the zero-penalty expansion `fenchelSmoothApproximation_zero_apply`;
- the owner-level comparison with the zero-penalty specialization
  `fenchelSmoothApproximation_zero_bounds`;
- the source-facing approximation-error theorem below.

Source/core/bridge triage:
- source-facing: the error estimate itself;
- core/canonical: `fenchelSmoothApproximation`;
- bridge/view: the theorem identifying the unsmoothed Fenchel supremum with the `μ = 0`
  specialization of that owner, and the source-facing bridge from that owner-level comparison back
  to `f x`.

This item does not introduce a second unsmoothed owner. The previous local
`fenchelApproximationMaximand` / `fenchelApproximation` pair duplicated the Chapter 6 owner
`fenchelSmoothApproximation`; the unsmoothed model is only the zero-penalty specialization of that
owner, so this file now exposes it only as a bridge theorem.
-/

/-- Setting the smoothing parameter to `0` recovers the unsmoothed Fenchel supremum model. -/
@[simp] theorem fenchelSmoothApproximation_zero_apply
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (x : E) :
    fenchelSmoothApproximation B f 0 x =
      sSup ((fun s : Dual ℝ E ↦ (s x : EReal) - fenchelConjugate f s) ''
        dom (fenchelConjugate f)) := by
  simp [fenchelSmoothApproximation, fenchelSmoothApproximationMaximand]

-- Proof sketch: the upper bound follows because the smoothed maximand is obtained from the
-- unsmoothed one by subtracting the nonnegative penalty `(μ / 2) ‖s‖[B,*]^2`.
-- For the lower bound, use the domain estimate `‖s‖[B,*] ≤ L` on every dual point
-- contributing to the
-- supremum, so the penalization removes at most `(μ * L^2) / 2` from the Fenchel representation
-- of `f`.
/-- Under the dual-domain radius bound `‖s‖[B,*] ≤ L`, the zero-penalty specialization dominates
every smoothed value and differs from it by at most `((μ * L^2) / 2 : NNReal)`. This is the
owner-level smoothing comparison, before identifying the zero-penalty value with `f x`. -/
theorem fenchelSmoothApproximation_zero_bounds
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal)
    {μ L : NNReal}
    (x : E)
    (hdual : ∀ s ∈ dom (fenchelConjugate f), ‖s‖[B,*] ≤ L) :
    fenchelSmoothApproximation B f 0 x ≥ fenchelSmoothApproximation B f μ x ∧
      fenchelSmoothApproximation B f μ x ≥
        fenchelSmoothApproximation B f 0 x - ((μ * L ^ 2) / 2 : NNReal) := sorry

-- Proof sketch: apply the owner-level comparison `fenchelSmoothApproximation_zero_bounds` and
-- rewrite its zero-penalty endpoint with the source-facing representation hypothesis `hf`.
/-- Text 6.1.1-Smoothing Approximation Error: if `f` is represented by the Fenchel supremum model
associated to its Fenchel conjugate at `x`, equivalently by the zero-penalty specialization of
`fenchelSmoothApproximation` at that point, and every `s ∈ dom (fenchelConjugate f)` satisfies
the dual estimate
`‖s‖[B,*] ≤ L`, then the smoothed approximation `f_μ` lies between `f` and
`f - (μ * L^2) / 2` on the canonical `EReal` surface. -/
theorem fenchelSmoothApproximation_error_bounds
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal)
    {μ L : NNReal}
    (x : E)
    (hf : f x = fenchelSmoothApproximation B f 0 x)
    (hdual : ∀ s ∈ dom (fenchelConjugate f), ‖s‖[B,*] ≤ L)
    :
    f x ≥ fenchelSmoothApproximation B f μ x ∧
      fenchelSmoothApproximation B f μ x ≥
        f x - ((μ * L ^ 2) / 2 : NNReal) := by
  simpa [hf] using fenchelSmoothApproximation_zero_bounds B f x hdual

end
