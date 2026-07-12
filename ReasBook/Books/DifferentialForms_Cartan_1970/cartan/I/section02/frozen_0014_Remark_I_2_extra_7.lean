import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open scoped NNReal ENNReal Topology

universe u

variable {𝕜 : Type u} [RCLike 𝕜]

/-- Remark I.2-extra-7: if `r` is strictly smaller than the radius of convergence of the scalar
power series `S(X) = ∑ a_n X^n`, then the difference quotients
`((S (z + h) - S z) / h)` converge uniformly in `z` on the closed disk `‖z‖ ≤ r` to the
derivative `S'`. -/
-- Proof sketch: choose a slightly larger radius still inside the disk of convergence, use the
-- power-series expansion there to control the derivative on a common neighborhood of the closed
-- disk, and combine the termwise derivative formula from Proposition 7.1 with uniform convergence
-- of difference quotients to the derivative on compact subsets.
theorem scalar_series_difference_quotients_tendstoUniformlyOn_closedBall
    (a : ℕ → 𝕜) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < (ofScalars 𝕜 a).radius) :
    TendstoUniformlyOn
      (fun h z ↦ (ofScalarsSum a (z + h) - ofScalarsSum a z) / h)
      (deriv (ofScalarsSum a))
      (𝓝[≠] (0 : 𝕜))
      (Metric.closedBall (0 : 𝕜) (r : ℝ)) := by
  let f : 𝕜 → 𝕜 := ofScalarsSum a
  let p : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 a
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hr with ⟨q, hrq, hq⟩
  have hp0 : 0 < p.radius := lt_of_le_of_lt (by simp) hq
  have hp : HasFPowerSeriesOnBall f p 0 p.radius := by
    simpa [f, p] using p.hasFPowerSeriesOnBall hp0
  let K : Set 𝕜 := Metric.closedBall (0 : 𝕜) (q : ℝ)
  have hK_subset : K ⊆ Metric.eball (0 : 𝕜) p.radius := by
    intro z hz
    have hzq : ‖z‖ ≤ (q : ℝ) := by
      simpa [K, Metric.mem_closedBall, dist_eq_norm] using hz
    exact mem_eball_zero_iff.2 <| lt_of_le_of_lt (by exact_mod_cast hzq) hq
  have hdiff : ∀ z ∈ K, DifferentiableAt 𝕜 f z := by
    intro z hz
    exact (hp.analyticAt_of_mem (hK_subset hz)).differentiableAt
  have hcont_fderiv : ContinuousOn (fderiv 𝕜 f) K := by
    exact (hp.fderiv.continuousOn).mono hK_subset
  have hunif_fderiv : UniformContinuousOn (fderiv 𝕜 f) K :=
    (isCompact_closedBall (0 : 𝕜) (q : ℝ)).uniformContinuousOn_of_continuous hcont_fderiv
  refine Metric.tendstoUniformlyOn_iff.2 fun ε εpos ↦ ?_
  rcases (Metric.uniformContinuousOn_iff.1 hunif_fderiv) (ε / 2) (half_pos εpos) with
    ⟨δu, hδu_pos, hδu⟩
  let δ : ℝ := min δu ((q : ℝ) - r)
  have hqr_pos : 0 < (q : ℝ) - r := by
    exact sub_pos.2 (by exact_mod_cast hrq)
  have hδ_pos : 0 < δ := lt_min hδu_pos hqr_pos
  have hδ_le_u : δ ≤ δu := min_le_left _ _
  have hδ_le_qr : δ ≤ (q : ℝ) - r := min_le_right _ _
  have hball :
      ({0}ᶜ ∩ Metric.ball (0 : 𝕜) δ : Set 𝕜) ∈ 𝓝[({0}ᶜ : Set 𝕜)] (0 : 𝕜) :=
    inter_mem_nhdsWithin ({0}ᶜ : Set 𝕜) (Metric.ball_mem_nhds (0 : 𝕜) hδ_pos)
  refine Filter.mem_of_superset hball ?_
  intro h hh z hz
  have hh0 : h ≠ 0 := hh.1
  have hhd : ‖h‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hh.2
  have hzK : z ∈ K := by
    have hzr : ‖z‖ ≤ (r : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hzq : ‖z‖ ≤ (q : ℝ) := by
      exact hzr.trans (by exact_mod_cast hrq.le)
    simpa [K, Metric.mem_closedBall, dist_eq_norm] using hzq
  have hzhK : z + h ∈ K := by
    have hzq : ‖z‖ ≤ (r : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hnorm : ‖z + h‖ ≤ (q : ℝ) := by
      calc
        ‖z + h‖ ≤ ‖z‖ + ‖h‖ := norm_add_le _ _
        _ ≤ (r : ℝ) + δ := add_le_add hzq hhd.le
        _ ≤ (q : ℝ) := by linarith
    simpa [K, Metric.mem_closedBall, dist_eq_norm] using hnorm
  let S : Set 𝕜 := Metric.closedBall z ‖h‖
  have hS_subset : S ⊆ K := by
    intro w hw
    have hwz : dist w z ≤ ‖h‖ := by
      simpa [S, Metric.mem_closedBall] using hw
    have hwq : ‖w‖ ≤ (q : ℝ) := by
      calc
        ‖w‖ = dist w 0 := by simp [dist_eq_norm]
        _ ≤ dist w z + dist z 0 := dist_triangle _ _ _
        _ ≤ ‖h‖ + ‖z‖ := by
          exact add_le_add (by simpa [dist_eq_norm] using hwz) (by simp [dist_eq_norm])
        _ ≤ δ + (r : ℝ) := add_le_add hhd.le (by simpa [dist_eq_norm] using hz)
        _ ≤ (q : ℝ) := by linarith
    simpa [K, Metric.mem_closedBall, dist_eq_norm] using hwq
  have hbound : ∀ w ∈ S, ‖fderiv 𝕜 f w - fderiv 𝕜 f z‖ ≤ ε / 2 := by
    intro w hw
    have hwK : w ∈ K := hS_subset hw
    have hwz : dist w z < δu := by
      have hwz' : dist w z ≤ ‖h‖ := by
        simpa [S, Metric.mem_closedBall] using hw
      exact lt_of_le_of_lt hwz' (lt_of_lt_of_le hhd hδ_le_u)
    exact le_of_lt <| by
      simpa [dist_eq_norm] using hδu w hwK z hzK hwz
  have hmv :
      ‖f (z + h) - f z - (fderiv 𝕜 f z) h‖ ≤ (ε / 2) * ‖h‖ := by
    have hmv' :
        ∀ ⦃x y : 𝕜⦄, x ∈ S → y ∈ S →
          ‖f y - f x - (fderiv 𝕜 f z) (y - x)‖ ≤ (ε / 2) * ‖y - x‖ := by
      intro x y hx hy
      exact (convex_closedBall z ‖h‖).norm_image_sub_le_of_norm_fderiv_le'
        (fun w hw ↦ hdiff w (hS_subset hw)) hbound hx hy
    have hzS : z ∈ S := by
      simp [S, Metric.mem_closedBall]
    have hzhS : z + h ∈ S := by
      simp [S, Metric.mem_closedBall, dist_eq_norm]
    simpa [sub_eq_add_neg, S, Metric.mem_closedBall, dist_eq_norm] using
      hmv' hzS hzhS
  have hdist :
      dist (deriv f z) ((f (z + h) - f z) / h) =
        ‖h⁻¹ • (f (z + h) - f z - (fderiv 𝕜 f z) h)‖ := by
    rw [dist_comm, dist_eq_norm]
    calc
      ‖(f (z + h) - f z) / h - deriv f z‖
          = ‖h⁻¹ * (f (z + h) - f z) - deriv f z‖ := by
              simp [div_eq_mul_inv, mul_comm]
      _ = ‖h⁻¹ * (f (z + h) - f z) - h⁻¹ * (h * deriv f z)‖ := by
            have hcancel : deriv f z = h⁻¹ * (h * deriv f z) := by
              field_simp [hh0]
            simpa using
              congrArg norm (congrArg (fun t ↦ h⁻¹ * (f (z + h) - f z) - t) hcancel)
      _ = ‖h⁻¹ * (f (z + h) - f z - h * deriv f z)‖ := by ring
      _ = ‖h⁻¹ • (f (z + h) - f z - (fderiv 𝕜 f z) h)‖ := by
            simp [smul_eq_mul, fderiv_eq_smul_deriv, mul_comm]
  calc
    dist (deriv f z) ((f (z + h) - f z) / h)
        = ‖h⁻¹ • (f (z + h) - f z - (fderiv 𝕜 f z) h)‖ := hdist
    _ ≤ ‖h⁻¹‖ * ‖f (z + h) - f z - (fderiv 𝕜 f z) h‖ := norm_smul_le _ _
    _ ≤ ‖h⁻¹‖ * ((ε / 2) * ‖h‖) := by
      exact mul_le_mul_of_nonneg_left hmv (norm_nonneg _)
    _ = ‖h‖⁻¹ * ((ε / 2) * ‖h‖) := by simp [norm_inv]
    _ = ε / 2 := by
      field_simp [norm_pos_iff.2 hh0, mul_comm, mul_left_comm, mul_assoc]
    _ < ε := half_lt_self εpos
