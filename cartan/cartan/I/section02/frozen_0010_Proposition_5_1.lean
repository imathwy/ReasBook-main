import Mathlib
import cartan.I.section02.«frozen_0004_Definition_I_2_extra_3»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open scoped NNReal ENNReal PowerSeries
open PowerSeries

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

-- Proof sketch: apply the summability control for the composition of analytic power series to
-- the scalar series attached to `S` and `T`. The source assumption
-- `T(X) = ∑_{n ≥ 1} b_n X^n` is recorded as `T.constantCoeff = 0`; with this hypothesis the
-- absolute-value majorant has no constant term, so a sufficiently small positive radius places it
-- strictly inside the disk of convergence of `S`.
/-- Proposition 5.1: if `S(X) = ∑ a_n X^n` and `T(X) = ∑_{n≥1} b_n X^n` have nonzero radii of
convergence, then there is a positive radius `r` for which the absolute-value majorant
`∑ ‖b_n‖ r^n` is strictly smaller than the radius of convergence of `S`. -/
theorem exists_pos_scalar_series_comp_majorant
    (S T : 𝕜⟦X⟧) (hT0 : T.constantCoeff = 0)
    (hS : S.radius ≠ 0)
    (hT : T.radius ≠ 0) :
    ∃ r : ℝ≥0, 0 < r ∧
      (∑' n : ℕ, (‖coeff n T‖₊ : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) <
        S.radius := sorry

-- Proof sketch: combine the positive witness radius from
-- `exists_pos_scalar_series_comp_majorant` with the canonical lower-bound theorem
-- `FormalMultilinearSeries.le_comp_radius_of_summable`, applied to the scalar series attached to
-- `S` and `T`.
/-- If `T(0) = 0`, then the substituted scalar series `S.subst T` still has nonzero radius of
convergence. -/
theorem scalar_series_comp_radius_ne_zero
    (S T : 𝕜⟦X⟧) (hT0 : T.constantCoeff = 0)
    (hS : S.radius ≠ 0)
    (hT : T.radius ≠ 0) :
    (ofScalars 𝕜 (fun n ↦ coeff n (S.subst T))).radius ≠ 0 := sorry

-- Proof sketch: estimate `‖T(z)‖` by the scalar majorant `∑ ‖coeff n T‖ r^n` whenever `‖z‖ ≤ r`,
-- and then use the strict inequality assumed for this majorant.
/-- If `‖z‖ ≤ r` and the majorant `∑ ‖b_n‖ r^n` is strictly below the radius of `S`, then
`‖T(z)‖` also lies strictly inside the disk of convergence of `S`. -/
theorem scalar_series_comp_right_eval_lt_left_radius
    (S T : 𝕜⟦X⟧) {r : ℝ≥0}
    (h : (∑' n : ℕ, (‖coeff n T‖₊ : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) <
      S.radius)
    {z : 𝕜} (hz : ‖z‖₊ ≤ r) :
    (‖T.sum z‖₊ : ℝ≥0∞) < S.radius := sorry

-- Proof sketch: use `T.constantCoeff = 0` to record the substitution side condition, apply
-- analytic composition for the scalar series attached to `S` and `T`, and evaluate the resulting
-- identity at any `z` with `‖z‖ ≤ r`.
/-- Relation `(5.1)` for scalar power series: when `T(0) = 0` and `‖z‖ ≤ r` with
`∑ ‖b_n‖ r^n < ρ(S)`, evaluating `S` at `T(z)` agrees with the sum of the substituted formal power
series `S.subst T` at `z`. -/
theorem scalar_series_sum_comp_eq_comp_sum_of_le
    (S T : 𝕜⟦X⟧) (hT0 : T.constantCoeff = 0) {r : ℝ≥0}
    (h : (∑' n : ℕ, (‖coeff n T‖₊ : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) <
      S.radius)
    {z : 𝕜} (hz : ‖z‖₊ ≤ r) :
    S.sum (T.sum z) = PowerSeries.sum (S.subst T) z := sorry
