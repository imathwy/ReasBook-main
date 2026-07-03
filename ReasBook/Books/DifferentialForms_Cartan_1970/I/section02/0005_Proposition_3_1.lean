import Mathlib
import DifferentialForms_Cartan_1970.I.section02.«0002_Definition_I_2_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open scoped NNReal ENNReal Topology

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

-- Proof sketch: apply `FormalMultilinearSeries.summable_norm_mul_pow` to the scalar series
-- `ofScalars 𝕜 a` at radius `r`, and use the resulting summable majorant
-- `n ↦ ‖a n‖ * r ^ n` to bound `‖a n * z ^ n‖` uniformly for `z` in the closed ball.
/-- Proposition 3.1 (1): clause (a): for every closed disk strictly inside the radius of
convergence, the scalar power series `∑ a_n z^n` converges normally on that disk. -/
theorem scalar_series_normallyConvergentOn_closedBall_of_lt_radius
    (a : ℕ → 𝕜) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < (ofScalars 𝕜 a).radius) :
    NormallyConvergentOn (fun n z ↦ a n * z ^ n) (Metric.closedBall (0 : 𝕜) (r : ℝ)) := by
  have hnorm : ∀ n, ‖ofScalars 𝕜 a n‖₊ = ‖a n‖₊ := fun n ↦
    Subtype.ext (ofScalars_norm 𝕜 a n)
  refine ⟨fun n ↦ ‖a n‖₊ * r ^ n, ?_, ?_⟩
  · simpa [hnorm] using (ofScalars 𝕜 a).summable_nnnorm_mul_pow hr
  · intro n z hz
    rw [norm_mul, norm_pow]
    simpa using mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp hz) n)
      (norm_nonneg _)

-- Proof sketch: apply the chapter-level owner lemma
-- `NormallyConvergentOn.summable_norm_apply` to Proposition `3.1 (1)` on the closed ball of radius
-- `‖z‖`.
/-- Proposition 3.1 (2): clause (a), in particular: at every point strictly inside the radius of
convergence, the scalar power series `∑ a_n z^n` converges absolutely. -/
theorem scalar_series_summable_norm_of_mem_radius
    (a : ℕ → 𝕜) {z : 𝕜} (hz : (‖z‖₊ : ℝ≥0∞) < (ofScalars 𝕜 a).radius) :
    Summable (fun n ↦ ‖a n * z ^ n‖) := by
  exact
    (scalar_series_normallyConvergentOn_closedBall_of_lt_radius a hz).summable_norm_apply
      (mem_closedBall_zero_iff.mpr le_rfl)

-- Proof sketch: rewrite `Summable (fun n ↦ a n * z ^ n)` as summability of the canonical norm
-- majorant `n ↦ ‖ofScalars 𝕜 a n‖ * ‖z‖ ^ n`, then apply the owner theorem
-- `FormalMultilinearSeries.not_summable_norm_of_radius_lt_nnnorm`.
/-- Proposition 3.1 (3): clause (b): at every point strictly outside the radius of convergence,
the scalar power series `∑ a_n z^n` is not summable. -/
theorem scalar_series_not_summable_of_radius_lt_norm
    (a : ℕ → 𝕜) {z : 𝕜} (hz : (ofScalars 𝕜 a).radius < (‖z‖₊ : ℝ≥0∞)) :
    ¬ Summable (fun n ↦ a n * z ^ n) := by
  intro hs
  have hs0 : Filter.Tendsto (fun n ↦ ‖a n * z ^ n‖) Filter.atTop (𝓝 0) :=
    tendsto_norm_zero.comp hs.tendsto_atTop_zero
  have hs' : Filter.Tendsto (fun n ↦ ‖(ofScalars 𝕜 a) n‖ * ‖z‖ ^ n) Filter.atTop (𝓝 0) := by
    simpa [Function.comp, ofScalars_norm, norm_mul, norm_pow, mul_comm, mul_left_comm, mul_assoc]
      using hs0
  exact not_le_of_gt hz ((ofScalars 𝕜 a).le_radius_of_tendsto hs')
