import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_7_13 (from Items/Chap07) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: combine the one-variable concavity theorem `Real.concaveOn_rpow` for the two
-- coordinate functions with `ConcaveOn.mul`; the required antitonicity on the nonnegative quadrant
-- comes from the exponents `α` and `1 - α` moving in opposite directions.
/-- The weighted geometric mean `(x, y) ↦ x^α y^(1-α)` is concave on the nonnegative quadrant for
weights `α ∈ [0, 1]`. -/
private theorem concaveOn_nonneg_weightedGeometricMean {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))
      (fun z : ℝ × ℝ ↦ z.1.rpow α * z.2.rpow (1 - α)) := sorry

-- Proof sketch: apply `ConcaveOn.le_map_integral` to the random vector `ω ↦ (X ω, Y ω)` and the
-- private concavity lemma above; integrability of the integrand follows from weighted AM-GM, and
-- the right-hand side uses the nonnegativity of the expectations obtained from
-- `integral_nonneg_of_ae`.
/-- Example 7.13: if `α ∈ [0,1]` and `X`, `Y` are nonnegative integrable random variables, then
the expectation of `X^α Y^(1-α)` is bounded above by the weighted geometric mean of the
expectations of `X` and `Y`, i.e. Jensen's inequality for the concave map
`(x, y) ↦ x^α y^(1-α)` on the nonnegative quadrant. -/
theorem expectation_weighted_geometricMean_le_weighted_geometricMean_expectations
    {P : Measure Ω} [IsProbabilityMeasure P] {α : ℝ} {X Y : Ω → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hX : Integrable X P) (hY : Integrable Y P)
    (hX_nonneg : 0 ≤ᵐ[P] X) (hY_nonneg : 0 ≤ᵐ[P] Y) :
    P[fun ω ↦ (X ω).rpow α * (Y ω).rpow (1 - α)] ≤
      (P[X]).rpow α * (P[Y]).rpow (1 - α) := sorry
