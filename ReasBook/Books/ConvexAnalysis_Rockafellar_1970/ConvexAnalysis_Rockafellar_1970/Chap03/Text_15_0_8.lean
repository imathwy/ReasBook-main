import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_12
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_24

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped GaugePolar

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.8 gives a concrete planar gauge
  `k(ξ₁, ξ₂) = √(ξ₁² + ξ₂²) + ξ₁`, computes its polar explicitly, and records that neither `k`
  nor `kᵒ` is a norm.
- `core/canonical`: the owner abstractions already present in the chapter are `IsClosedGauge`,
  `gauge_polar`, `IsGaugeNorm`, and the project's canonical planar ambient
  `R2 = EuclideanSpace ℝ (Fin 2)`.
- `bridge/view`: the file keeps the source-facing explicit primal formula as data and puts the
  displayed polar formula directly on the theorem surface, without introducing an extra polar owner
  or a second ambient-space wrapper for the example.

Domain-style sampling used here:
- `IsGauge` from `Text_15_0_1`;
- `IsGauge.eq_egauge_unitSublevel` from `Text_15_0_2`, showing the canonical set-side owner
  available for gauges after the gauge structure is known;
- `gauge_polar` from `Text_15_0_5`;
- `IsClosedGauge` from `Text_15_0_24`, the chapter owner for a closed gauge;
- `IsGaugeNorm` from `Text_15_0_12`.
- the nearby planar-example owners `R2 = EuclideanSpace ℝ (Fin 2)` in `Text_14_0_14` and
  `Text_15_0_27`, showing the chapter's canonical ambient model for source-facing `R²` formulas.

Primitive data vs derived API:
- primitive source data: the explicit planar formula `parabolicGauge`;
- derived API: the owner-predicate fact `parabolicGauge_isClosedGauge`, the theorem giving the
  displayed piecewise formula for `parabolicGaugeᵒ`, and the statements that neither the primal nor
  the polar gauge is a norm-gauge.

Layer target: `source-facing`. The explicit formula from the text remains the public core, while
the closed-gauge owner abstraction `IsClosedGauge` is reused directly for clause (1), and the
polar clause is kept as a theorem-level displayed formula rather than a second public owner. The
public ambient is the chapter's canonical planar owner layer `R2`, matching the recurring
coordinate-example API already shared elsewhere in the project.
-/

/-- The concrete gauge on `R²` given by `k(ξ₁, ξ₂) = √(ξ₁² + ξ₂²) + ξ₁`. -/
def parabolicGauge : R2 → EReal :=
  fun x ↦
    ((Real.sqrt (x 0 ^ 2 + x 1 ^ 2) + x 0 : ℝ) : EReal)

-- Proof sketch: the epigraph of `parabolicGauge` is the closed second-order cone
-- `{(ξ, t) | Real.sqrt (ξ₁^2 + ξ₂^2) + ξ₁ ≤ t}`. This gives both the gauge axioms and lower
-- semicontinuity, so clause (1) is stated directly with the Chapter 15 owner `IsClosedGauge`.
/-- Text 15.0.8 (1): the function `k(ξ₁, ξ₂) = √(ξ₁² + ξ₂²) + ξ₁` is a closed gauge on `R²`. -/
theorem parabolicGauge_isClosedGauge :
    IsClosedGauge parabolicGauge := sorry

-- Proof sketch: start from the definition of `parabolicGaugeᵒ` as the infimum of all scalar
-- majorants `μ⋆` satisfying `⟪x, x⋆⟫ ≤ μ⋆ k x`. Optimize this inequality using the explicit
-- formula for `k`; the admissible majorants are exactly the displayed piecewise family.
/-- Text 15.0.8 (2): the polar gauge of `k` is the displayed piecewise function with finite value
`((ξ₂^*)² / ξ₁^* + ξ₁^*) / 2` when `ξ₁^* > 0`, value `0` at the origin, and value `+∞`
otherwise. -/
theorem gauge_polar_parabolicGauge_eq (xStar : R2) :
    parabolicGaugeᵒ xStar =
      if 0 < xStar 0 then
        (((xStar 1 ^ 2 / xStar 0 + xStar 0) / 2 : ℝ) : EReal)
      else if xStar = 0 then
        0
      else
        ⊤ := sorry

-- Proof sketch: a norm-gauge must be symmetric. For `x = (ξ₁, ξ₂)`, one has
-- `parabolicGauge (-x) = √(ξ₁² + ξ₂²) - ξ₁`, which differs from `parabolicGauge x` whenever
-- `ξ₁ ≠ 0`. Hence `parabolicGauge` cannot satisfy the symmetry field of `IsGaugeNorm`.
/-- Text 15.0.8 (3): the gauge `k` is not a norm. -/
theorem parabolicGauge_not_isGaugeNorm :
    ¬ IsGaugeNorm parabolicGauge := sorry

-- Proof sketch: the polar formula from the preceding clause gives
-- `parabolicGaugeᵒ xStar = ⊤` whenever the first coordinate of `xStar` is negative, so
-- `parabolicGaugeᵒ` is not finite everywhere. Since finiteness at every point is required in
-- `IsGaugeNorm`, the polar gauge cannot be a norm.
/-- Text 15.0.8 (4): the polar gauge `kᵒ` is not a norm. -/
theorem gauge_polar_parabolicGauge_not_isGaugeNorm :
    ¬ IsGaugeNorm parabolicGaugeᵒ := sorry

end
