import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Cartan section06 0019_Exercise_4: Exercise 4: if `f` is continuous on the closed disc
`|z| ≤ r`, then the circle integrals on
the concentric circles of radii `((1 : ℝ) - 1 / (n + 1 : ℝ)) * r` converge to the circle integral
on the boundary circle of radius `r`. -/
-- Proof sketch: unfold `circleIntegral` into an interval integral over `circleMap 0 R`; then apply
-- dominated convergence on `[0, 2 * π]`, using continuity of `f` on the closed disc for the
-- pointwise limit and compactness of the closed disc for a uniform bound on the integrands.
theorem circleIntegral_tendsto_shrinking_radii_of_continuousOn_closedBall
    {f : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r) (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) r)) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∮ z in C((0 : ℂ), ((1 : ℝ) - 1 / (n + 1 : ℝ)) * r), f z)
      Filter.atTop
      (nhds (∮ z in C((0 : ℂ), r), f z)) := by
  let ρ : ℕ → ℝ := fun n ↦ (1 : ℝ) - 1 / (n + 1 : ℝ)
  let u : ℕ → ℂ → ℂ := fun n z ↦ (ρ n : ℂ) * f ((ρ n : ℂ) * z)
  -- The shrinking factors stay in `[0, 1]` and converge to `1`.
  have hρ_nonneg : ∀ n : ℕ, 0 ≤ ρ n := by
    intro n
    have hden_ge : (1 : ℝ) ≤ n + 1 := by
      have hn0 : (0 : ℝ) ≤ n := by positivity
      linarith
    have hdiv : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 := by
      simpa using (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hden_ge)
    dsimp [ρ]
    linarith
  have hρ_le_one : ∀ n : ℕ, ρ n ≤ 1 := by
    intro n
    dsimp [ρ]
    nlinarith [one_div_nonneg.mpr (show (0 : ℝ) ≤ n + 1 by positivity)]
  have hρ_tendsto_zero :
      Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1 : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hρ_tendsto : Filter.Tendsto ρ Filter.atTop (nhds 1) := by
    simpa [ρ, one_div] using tendsto_const_nhds.sub hρ_tendsto_zero
  -- On the fixed circle, radial contractions converge uniformly to the identity.
  have hradial :
      TendstoUniformlyOn
        (fun n (z : ℂ) ↦ (ρ n : ℂ) * z)
        (fun z ↦ z)
        Filter.atTop
        (Metric.sphere (0 : ℂ) r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rcases exists_pos_mul_lt hε r with ⟨δ, hδpos, hδr⟩
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hρ_tendsto_zero δ hδpos
    filter_upwards [Filter.eventually_ge_atTop N] with n hn z hz
    have hz_norm : ‖z‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
    have hsmall : (1 : ℝ) / (n + 1 : ℝ) < δ := by
      have hsmall' : |(n + 1 : ℝ)|⁻¹ < δ := by
        simpa [Real.dist_eq, one_div] using hN n hn
      have hden_nonneg : 0 ≤ (n + 1 : ℝ) := by positivity
      simpa [one_div, abs_of_nonneg hden_nonneg] using hsmall'
    have hsub :
        z - z * (ρ n : ℂ) = z * (((1 - ρ n : ℝ) : ℂ)) := by
      calc
        z - z * (ρ n : ℂ) = z * (1 - (ρ n : ℂ)) := by ring
        _ = z * (((1 - ρ n : ℝ) : ℂ)) := by simp
    calc
      dist (z) ((ρ n : ℂ) * z) = ‖z - z * (ρ n : ℂ)‖ := by
        simp [dist_eq_norm, mul_comm]
      _ = ‖z * (((1 - ρ n : ℝ) : ℂ))‖ := by rw [hsub]
      _ = r * (1 - ρ n) := by
        rw [norm_mul, hz_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr (hρ_le_one n))]
      _ = ((1 : ℝ) / (n + 1 : ℝ)) * r := by
        simp [ρ, mul_comm]
      _ < ε := by
        rcases lt_or_eq_of_le hr with (hr_pos | rfl)
        · have hmul : ((1 : ℝ) / (n + 1 : ℝ)) * r < δ * r := by
            exact mul_lt_mul_of_pos_right hsmall hr_pos
          have hδr' : δ * r < ε := by simpa [mul_comm] using hδr
          exact lt_trans hmul hδr'
        · simpa using hε
  -- Uniform continuity on the compact closed ball transfers the radial convergence through `f`.
  have huc :
      UniformContinuousOn f (Metric.closedBall (0 : ℂ) r) :=
    (isCompact_closedBall (0 : ℂ) r).uniformContinuousOn_of_continuous hf
  have hscaled_mem_closedBall :
      ∀ n : ℕ,
        Set.MapsTo
          (fun z : ℂ ↦ (ρ n : ℂ) * z)
          (Metric.sphere (0 : ℂ) r)
          (Metric.closedBall (0 : ℂ) r) := by
    intro n z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hz_norm : ‖z‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
    calc
      ‖(ρ n : ℂ) * z‖ = ‖(ρ n : ℂ)‖ * ‖z‖ := norm_mul _ _
      _ = ρ n * r := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ_nonneg n), hz_norm]
      _ ≤ r := by
        nlinarith [hρ_nonneg n, hρ_le_one n, hr]
  have hcomp :
      TendstoUniformlyOn
        (fun n (z : ℂ) ↦ f ((ρ n : ℂ) * z))
        f
        Filter.atTop
        (Metric.sphere (0 : ℂ) r) :=
    huc.comp_tendstoUniformlyOn_eventually
      (Filter.Eventually.of_forall hscaled_mem_closedBall)
      (fun z hz ↦ Metric.sphere_subset_closedBall hz)
      hradial
  have hbound :
      ∃ C, ∀ z ∈ Metric.closedBall (0 : ℂ) r, ‖f z‖ ≤ C :=
    (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn hf
  obtain ⟨C, hC⟩ := hbound
  have hzero_mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hr
  have hC_nonneg : 0 ≤ C := by
    have hC0 : ‖f 0‖ ≤ C := hC 0 hzero_mem
    exact le_trans (norm_nonneg _) hC0
  have hu :
      TendstoUniformlyOn u f Filter.atTop (Metric.sphere (0 : ℂ) r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hε_half : 0 < ε / 2 := by positivity
    have hC1_pos : 0 < C + 1 := by linarith
    obtain ⟨N, hN⟩ :=
      Metric.tendsto_atTop.1 hρ_tendsto_zero (ε / (2 * (C + 1))) (by positivity)
    have hcomp_half :
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ z ∈ Metric.sphere (0 : ℂ) r, dist (f ((ρ n : ℂ) * z)) (f z) < ε / 2 :=
      (Metric.tendstoUniformlyOn_iff.mp hcomp) (ε / 2) hε_half |>.mono fun n hn z hz => by
        simpa [dist_comm] using hn z hz
    filter_upwards [Filter.eventually_ge_atTop N, hcomp_half] with n hn hcompn z hz
    have hz_ball : z ∈ Metric.closedBall (0 : ℂ) r := Metric.sphere_subset_closedBall hz
    have hz_scaled_ball : (ρ n : ℂ) * z ∈ Metric.closedBall (0 : ℂ) r :=
      hscaled_mem_closedBall n hz
    have hz_bound : ‖f z‖ ≤ C := hC z hz_ball
    have hρ_small : |ρ n - 1| < ε / (2 * (C + 1)) := by
      have hsmall := hN n hn
      simpa [ρ, Real.dist_eq, sub_eq_add_neg, abs_neg,
        abs_of_nonneg (one_div_nonneg.2 (by positivity))] using hsmall
    have hfirst_norm : ‖f ((ρ n : ℂ) * z) - f z‖ < ε / 2 := by
      simpa [dist_eq_norm] using hcompn z hz
    have hfirst :
        ‖(ρ n : ℂ) * (f ((ρ n : ℂ) * z) - f z)‖ < ε / 2 := by
      have hfirst_le :
          ‖(ρ n : ℂ) * (f ((ρ n : ℂ) * z) - f z)‖ ≤ ‖f ((ρ n : ℂ) * z) - f z‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ_nonneg n)]
        nlinarith [hρ_le_one n, norm_nonneg (f ((ρ n : ℂ) * z) - f z)]
      exact lt_of_le_of_lt hfirst_le hfirst_norm
    have hsecond :
        ‖(((ρ n - 1 : ℝ) : ℂ) * f z)‖ < ε / 2 := by
      have hmul :
          |ρ n - 1| * (C + 1) < ε / 2 := by
        calc
          |ρ n - 1| * (C + 1) < (ε / (2 * (C + 1))) * (C + 1) :=
            mul_lt_mul_of_pos_right hρ_small hC1_pos
          _ = ε / 2 := by
            field_simp [hC1_pos.ne']
      calc
        ‖(((ρ n - 1 : ℝ) : ℂ) * f z)‖ = |ρ n - 1| * ‖f z‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ |ρ n - 1| * C := by
          exact mul_le_mul_of_nonneg_left hz_bound (abs_nonneg _)
        _ < ε / 2 := by
          have hle : |ρ n - 1| * C ≤ |ρ n - 1| * (C + 1) := by
            exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
          exact lt_of_le_of_lt hle hmul
    have hdecomp :
        u n z - f z =
          (ρ n : ℂ) * (f ((ρ n : ℂ) * z) - f z) + (((ρ n - 1 : ℝ) : ℂ) * f z) := by
      simp [u]
      ring
    calc
      dist (f z) (u n z) = ‖u n z - f z‖ := by
        rw [dist_comm, dist_eq_norm]
      _ =
          ‖(ρ n : ℂ) * (f ((ρ n : ℂ) * z) - f z) +
            (((ρ n - 1 : ℝ) : ℂ) * f z)‖ := by
          rw [hdecomp]
      _ ≤ ‖(ρ n : ℂ) * (f ((ρ n : ℂ) * z) - f z)‖ + ‖(((ρ n - 1 : ℝ) : ℂ) * f z)‖ :=
        norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hfirst hsecond
      _ = ε := by ring
  -- Each normalized integrand is continuous on the fixed circle.
  have hu_cont :
      ∀ᶠ n : ℕ in Filter.atTop, ContinuousOn (u n) (Metric.sphere (0 : ℂ) r) := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hscale_cont : Continuous (fun z : ℂ ↦ (ρ n : ℂ) * z) := by
      simpa using (continuous_const.mul continuous_id)
    have hcomp_cont :
        ContinuousOn (fun z : ℂ ↦ f ((ρ n : ℂ) * z)) (Metric.sphere (0 : ℂ) r) :=
      hf.comp hscale_cont.continuousOn (hscaled_mem_closedBall n)
    simpa [u] using (continuousOn_const.mul hcomp_cont)
  -- Re-express each shrinking-radius circle integral as a fixed-radius integral of `u n`.
  have hrescale :
      ∀ n : ℕ,
        (∮ z in C((0 : ℂ), r), u n z) = ∮ z in C((0 : ℂ), (ρ n) * r), f z := by
    intro n
    rw [circleIntegral_def_Icc, circleIntegral_def_Icc]
    refine MeasureTheory.integral_congr_ae <| Filter.Eventually.of_forall ?_
    intro θ
    simp only [u, deriv_circleMap, smul_eq_mul]
    have hcircle : (ρ n : ℂ) * circleMap 0 r θ = circleMap 0 ((ρ n) * r) θ := by
      calc
        (ρ n : ℂ) * circleMap 0 r θ = circleMap 0 (ρ n) 0 * circleMap 0 r θ := by
          simp [circleMap_zero]
        _ = circleMap 0 ((ρ n) * r) (0 + θ) := by
          rw [circleMap_zero_mul]
        _ = circleMap 0 ((ρ n) * r) θ := by simp
    rw [hcircle]
    calc
      circleMap 0 r θ * Complex.I * ((ρ n : ℂ) * f (circleMap 0 ((ρ n) * r) θ))
          = ((ρ n : ℂ) * circleMap 0 r θ) * Complex.I * f (circleMap 0 ((ρ n) * r) θ) := by
            ring
      _ = circleMap 0 ((ρ n) * r) θ * Complex.I * f (circleMap 0 ((ρ n) * r) θ) := by
            rw [hcircle]
  -- The fixed-radius convergence theorem now applies directly.
  have hfixed :
      Filter.Tendsto
        (fun n : ℕ ↦ ∮ z in C((0 : ℂ), r), u n z)
        Filter.atTop
        (nhds (∮ z in C((0 : ℂ), r), f z)) :=
    hu.tendsto_circleIntegral_of_continuousOn hr hu_cont
  convert hfixed using 1
  ext n
  symm
  simpa [ρ] using hrescale n
