import Mathlib
import cartan.I.section02.«frozen_0004_Definition_I_2_extra_3»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open PowerSeries
open scoped BigOperators NNReal ENNReal PowerSeries

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

-- Proof sketch: specialize `FormalMultilinearSeries.min_radius_le_radius_add` to the analytic
-- series attached to `S` and `T`, then compare the common lower bound `ρ` with the minimum of
-- the two radii.
/-- Proposition 4.1 (1): if two scalar power series have radius of convergence at least `ρ`, then
their coefficientwise sum also has radius of convergence at least `ρ`. -/
theorem scalar_series_sum_radius_ge
    (S T : 𝕜⟦X⟧) (ρ : ℝ≥0)
    (hS : (ρ : ℝ≥0∞) ≤ S.radius)
    (hT : (ρ : ℝ≥0∞) ≤ T.radius) :
    (ρ : ℝ≥0∞) ≤ (S + T).radius := by
  calc
    (ρ : ℝ≥0∞) ≤ min S.radius T.radius := le_min hS hT
    _ ≤ ((ofScalars 𝕜 (fun n ↦ coeff n S)) + (ofScalars 𝕜 (fun n ↦ coeff n T))).radius := by
      simpa [PowerSeries.radius] using
        min_radius_le_radius_add (ofScalars 𝕜 (fun n ↦ coeff n S))
          (ofScalars 𝕜 (fun n ↦ coeff n T))
    _ = (S + T).radius := by
      have hcoeff :
          (fun n ↦ coeff n (S + T)) = (fun n ↦ coeff n S) + fun n ↦ coeff n T := by
        ext n
        simp
      rw [PowerSeries.radius, hcoeff, ofScalars_add]

-- Proof sketch: for every `r < ρ`, the absolute-value coefficient series for `a` and `b` are
-- summable; apply the Cauchy-product summability theorem to the coefficient sequence of `S * T`,
-- then use
-- `le_radius_of_summable` to deduce the same lower bound for the product radius.
/-- Proposition 4.1 (2): if two scalar power series have radius of convergence at least `ρ`, then
their Cauchy product also has radius of convergence at least `ρ`. -/
theorem scalar_series_cauchy_product_radius_ge
    (S T : 𝕜⟦X⟧) (ρ : ℝ≥0)
    (hS : (ρ : ℝ≥0∞) ≤ S.radius)
    (hT : (ρ : ℝ≥0∞) ≤ T.radius) :
    (ρ : ℝ≥0∞) ≤ (S * T).radius :=
    sorry

section Complete

variable [CompleteSpace 𝕜]

-- Proof sketch: inside the common convergence disk, both scalar series are summable absolutely, so
-- the series attached to `S + T` may be summed termwise and identified with the sum of the two
-- evaluated series.
/-- Proposition 4.1 (3): for `‖z‖ < ρ`, evaluating the coefficientwise sum series at `z` gives the
sum of the two scalar series evaluated at `z`. -/
theorem scalar_series_sum_eval_eq_add
    (S T : 𝕜⟦X⟧) (ρ : ℝ≥0)
    (hS : (ρ : ℝ≥0∞) ≤ S.radius)
    (hT : (ρ : ℝ≥0∞) ≤ T.radius)
    {z : 𝕜} (hz : ‖z‖₊ < ρ) :
    PowerSeries.sum (S + T) z = S.sum z + T.sum z := sorry

-- Proof sketch: for `‖z‖ < ρ`, the two scalar series are absolutely convergent; apply the Cauchy
-- product theorem to the coefficient sequence of `S * T` and then identify the resulting sum with
-- the value of `PowerSeries.sum`.
/-- Proposition 4.1 (4): for `‖z‖ < ρ`, evaluating the Cauchy-product series at `z` gives the
product of the two scalar series evaluated at `z`. -/
theorem scalar_series_cauchy_product_eval_eq_mul
    (S T : 𝕜⟦X⟧) (ρ : ℝ≥0)
    (hS : (ρ : ℝ≥0∞) ≤ S.radius)
    (hT : (ρ : ℝ≥0∞) ≤ T.radius)
    {z : 𝕜} (hz : ‖z‖₊ < ρ) :
    PowerSeries.sum (S * T) z = S.sum z * T.sum z := sorry

end Complete
