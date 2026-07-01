import Mathlib
import cartan.I.section04.«0004_Proposition_2_2»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries

universe u

variable {𝕜 : Type u} [RCLike 𝕜]

/-
Remark 2 is `source-facing`: the textbook statement is about normalized iterated derivatives.
Its `core/canonical` owner is the coefficient of the recentered scalar power series
`(ofScalars 𝕜 a).changeOrigin x`.
-/
/-- Core/canonical coefficient estimate underlying Remark 2. -/
theorem norm_changeOrigin_coeff_le_powerSeriesAbsSum
    (a : ℕ → 𝕜) (p : ℕ) {r r₀ : ℝ} {x : 𝕜}
    (hr : ENNReal.ofReal r < (ofScalars 𝕜 a).radius)
    (hx : ‖x‖ ≤ r₀) (hr₀ : r₀ < r) :
    ‖((ofScalars 𝕜 a).changeOrigin x).coeff p‖ ≤
      ofScalarsSum (fun n ↦ ‖a n‖) r / (r - r₀) ^ p := sorry

/-- Remark 2: if `r` lies strictly inside the radius of convergence and `‖x‖ ≤ r₀ < r`, then the
normalized `p`-th derivative of the summed scalar power series is bounded by
`A(r) / (r - r₀)^p`, where `A(r)` is the canonical scalar-series sum
`ofScalarsSum (fun n ↦ ‖a n‖) r = ∑ |a_n| r^n`. -/
-- Proof sketch: differentiate the scalar power series termwise `p` times, divide by `p!`, use
-- `‖x‖ ≤ r₀ < r` to bound each term by the geometric majorant at radius `r`, and then sum the
-- resulting estimate.
theorem norm_iteratedDeriv_ofScalarsSum_div_factorial_le_powerSeriesAbsSum
    (a : ℕ → 𝕜) (p : ℕ) {r r₀ : ℝ} {x : 𝕜}
    (hr : ENNReal.ofReal r < (ofScalars 𝕜 a).radius)
    (hx : ‖x‖ ≤ r₀) (hr₀ : r₀ < r) :
    ‖iteratedDeriv p (ofScalarsSum a) x / (p.factorial : 𝕜)‖ ≤
      ofScalarsSum (fun n ↦ ‖a n‖) r / (r - r₀) ^ p := by
  have hr₀_nonneg : 0 ≤ r₀ := le_trans (norm_nonneg x) hx
  have hr_pos : 0 < r := lt_of_le_of_lt hr₀_nonneg hr₀
  have hxr : ‖x‖ < r := lt_of_le_of_lt hx hr₀
  have hseries :
      HasFPowerSeriesOnBall (ofScalarsSum a) (ofScalars 𝕜 a) 0 (ENNReal.ofReal r) := by
    have hq_pos : 0 < (ofScalars 𝕜 a).radius :=
      lt_of_le_of_lt bot_le hr
    exact
      ((ofScalars 𝕜 a).hasFPowerSeriesOnBall hq_pos).mono
        (ENNReal.ofReal_pos.mpr hr_pos) hr.le
  simpa [scalar_changeOrigin_coeff_eq_iteratedDeriv_div_factorial hseries hxr p] using
    norm_changeOrigin_coeff_le_powerSeriesAbsSum a p hr hx hr₀
