import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was unavailable in this environment; this statement uses
-- mathlib's canonical `circleMap` and interval-integral surface for the Poisson kernel.

open Complex Filter Metric Set

/-- Helper for Lemma IV.4-extra-4: if the angular cutoff is at least `π`, then the excluded-angle
set is empty because angle representatives always lie in `[-π, π]`. -/
lemma cutoff_set_eq_empty_of_pi_le {θ₀ η : ℝ} (hπη : Real.pi ≤ η) :
    {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|} = ∅ := by
  -- The cutoff is impossible once `η` dominates the universal `π` bound for `Angle.toReal`.
  ext θ
  simp [not_lt.mpr <| (Real.Angle.abs_toReal_le_pi _).trans hπη]

/-- Helper for Lemma IV.4-extra-4: the distance between two points on the circle only depends on
the representative of their angular difference. -/
lemma circle_distance_eq_two_mul_sin_half_toReal
    {r θ θ₀ : ℝ} (hr : 0 < r) :
    ‖circleMap 0 r θ - circleMap 0 r θ₀‖ =
      2 * r * |Real.sin ((((θ - θ₀ : Real.Angle)).toReal) / 2)| := by
  let δ : ℝ := ((θ - θ₀ : Real.Angle)).toReal
  have hδ : ((δ : ℝ) : Real.Angle) = (θ - θ₀ : Real.Angle) := by
    simp [δ]
  have hsum : ((δ + θ₀ : ℝ) : Real.Angle) = (θ : Real.Angle) := by
    have := congrArg (fun x : Real.Angle => x + (θ₀ : Real.Angle)) hδ
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  have hcircle : circleMap 0 r (δ + θ₀) = circleMap 0 r θ := by
    rw [circleMap_eq_circleMap_iff 0 (by positivity)]
    rcases (Real.Angle.angle_eq_iff_two_pi_dvd_sub).mp hsum with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hk' : δ + θ₀ = θ + (k : ℝ) * (2 * Real.pi) := by
      linarith
    simpa [add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun t : ℝ => t * Complex.I) hk'
  have hmul : circleMap 0 r (δ + θ₀) = circleMap 0 r θ₀ * circleMap 0 1 δ := by
    simpa [mul_one, add_comm] using (circleMap_zero_mul r 1 θ₀ δ).symm
  have hfactor :
      circleMap 0 r (δ + θ₀) - circleMap 0 r θ₀ =
        circleMap 0 r θ₀ * (circleMap 0 1 δ - 1) := by
    rw [hmul]
    ring
  have hnorm_exp : ‖circleMap 0 1 δ - 1‖ = 2 * |Real.sin (δ / 2)| := by
    simpa [circleMap_zero, mul_comm, Real.norm_eq_abs] using Complex.norm_exp_I_mul_ofReal_sub_one δ
  -- Rewrite one point by the canonical representative of the angle difference, then factor.
  calc
    ‖circleMap 0 r θ - circleMap 0 r θ₀‖ = ‖circleMap 0 r (δ + θ₀) - circleMap 0 r θ₀‖ := by
      rw [hcircle]
    _ = ‖circleMap 0 r θ₀ * (circleMap 0 1 δ - 1)‖ := by
      exact congrArg norm hfactor
    _ = ‖circleMap 0 r θ₀‖ * ‖circleMap 0 1 δ - 1‖ := norm_mul _ _
    _ = r * ‖circleMap 0 1 δ - 1‖ := by simp [norm_circleMap_zero, abs_of_pos hr]
    _ = r * (2 * |Real.sin (δ / 2)|) := by
      rw [hnorm_exp]
    _ = 2 * r * |Real.sin (δ / 2)| := by ring

/-- Helper for Lemma IV.4-extra-4: on the angular region staying `η` away from `θ₀`, the boundary
circle stays at least `2 * r * sin (η / 2)` away from `circleMap 0 r θ₀`. -/
lemma away_arc_has_positive_distance
    {r θ₀ η θ : ℝ} (hr : 0 < r) (hη : 0 < η) (hηπ : η < Real.pi)
    (hcut : η ≤ |((θ - θ₀ : Real.Angle)).toReal|) :
    2 * r * Real.sin (η / 2) ≤ ‖circleMap 0 r θ - circleMap 0 r θ₀‖ := by
  let δ : ℝ := ((θ - θ₀ : Real.Angle)).toReal
  have hδ_le : |δ| ≤ Real.pi := by
    simpa [δ] using Real.Angle.abs_toReal_le_pi (θ - θ₀ : Real.Angle)
  have hη_half_mem : η / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hη, hηπ]
  have hδ_half_mem : |δ| / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [abs_nonneg δ, hδ_le]
  have hsin_mono :
      Real.sin (η / 2) ≤ Real.sin (|δ| / 2) := by
    refine Real.monotoneOn_sin hη_half_mem hδ_half_mem ?_
    linarith
  have hsin_abs :
      |Real.sin (δ / 2)| = Real.sin (|δ| / 2) := by
    have hhalf_le_pi : |δ / 2| ≤ Real.pi := by
      calc
        |δ / 2| = |δ| / 2 := by
          rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        _ ≤ Real.pi / 2 := by
          gcongr
        _ ≤ Real.pi := by linarith [Real.pi_pos]
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi]
    · rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    · exact hhalf_le_pi
  -- The chord-length formula converts the angular gap into a uniform metric gap.
  calc
    2 * r * Real.sin (η / 2) ≤ 2 * r * |Real.sin (δ / 2)| := by
      rw [hsin_abs]
      gcongr
    _ = ‖circleMap 0 r θ - circleMap 0 r θ₀‖ := by
      simpa [δ] using (circle_distance_eq_two_mul_sin_half_toReal (θ := θ) (θ₀ := θ₀) hr).symm

/-- Helper for Lemma IV.4-extra-4: once the denominator is uniformly bounded below by `m`, the
indicator-truncated Poisson kernel is uniformly bounded by `(r^2 - ‖z‖^2) / m^2`. -/
lemma poisson_kernel_indicator_norm_le
    {r θ₀ η m : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) (hm : 0 < m)
    (hsep :
      ∀ θ : ℝ, η < |((θ - θ₀ : Real.Angle)).toReal| → m ≤ ‖circleMap 0 r θ - z‖)
    (θ : ℝ) :
    ‖indicator {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
        (fun θ : ℝ ↦ poissonKernel 0 z (circleMap 0 r θ)) θ‖
      ≤ (r ^ 2 - ‖z‖ ^ 2) / m ^ 2 := by
  have hnorm_lt : ‖z‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg z) hnorm_lt
  have hnum_nonneg : 0 ≤ r ^ 2 - ‖z‖ ^ 2 := by
    nlinarith [norm_nonneg z, hnorm_lt]
  by_cases hcut : η < |((θ - θ₀ : Real.Angle)).toReal|
  · have hden_le : m ^ 2 ≤ ‖circleMap 0 r θ - z‖ ^ 2 := by
      nlinarith [hsep θ hcut]
    have hm_sq_pos : 0 < m ^ 2 := sq_pos_of_pos hm
    have hkernel_nonneg :
        0 ≤
          (‖circleMap 0 r θ - (0 : ℂ)‖ ^ 2 - ‖z - 0‖ ^ 2) /
            ‖(circleMap 0 r θ - 0) - (z - 0)‖ ^ 2 := by
      refine div_nonneg ?_ (sq_nonneg _)
      simpa [sub_zero, norm_circleMap_zero, abs_of_pos hr] using hnum_nonneg
    have hkernel_le :
        (‖circleMap 0 r θ - (0 : ℂ)‖ ^ 2 - ‖z - 0‖ ^ 2) /
            ‖(circleMap 0 r θ - 0) - (z - 0)‖ ^ 2
          ≤ (r ^ 2 - ‖z‖ ^ 2) / m ^ 2 := by
      simpa [sub_zero, norm_circleMap_zero, abs_of_pos hr, sub_eq_add_neg, sq] using
        div_le_div_of_nonneg_left hnum_nonneg hm_sq_pos hden_le
    -- On the cutoff set, the kernel formula is controlled by the lower denominator bound.
    simp [hcut]
    simpa [Real.norm_eq_abs, poissonKernel_def, sub_zero, norm_circleMap_zero, abs_of_pos hr,
      sub_eq_add_neg, sq] using (show
        |(‖circleMap 0 r θ - (0 : ℂ)‖ ^ 2 - ‖z - 0‖ ^ 2) /
            ‖(circleMap 0 r θ - 0) - (z - 0)‖ ^ 2| ≤ (r ^ 2 - ‖z‖ ^ 2) / m ^ 2 from by
        exact (abs_of_nonneg hkernel_nonneg).symm ▸ hkernel_le)
  · -- Outside the cutoff set, the indicator kills the integrand.
    simp [hcut, hnum_nonneg, div_nonneg, hm.le]

/-- Helper for Lemma IV.4-extra-4: the radial factor in the Poisson kernel vanishes as `z`
approaches the boundary point `circleMap 0 r θ₀`. -/
lemma radial_gap_tendsto_zero {r θ₀ : ℝ} (hr : 0 < r) :
    Tendsto (fun z : ℂ ↦ r ^ 2 - ‖z‖ ^ 2)
      (nhdsWithin (circleMap 0 r θ₀) (ball (0 : ℂ) r)) (nhds 0) := by
  have hcont : Continuous fun z : ℂ ↦ r ^ 2 - ‖z‖ ^ 2 := by
    fun_prop
  -- The limiting value is zero because the boundary point has norm exactly `r`.
  have hzero : r ^ 2 - ‖circleMap 0 r θ₀‖ ^ 2 = 0 := by
    simp [norm_circleMap_zero, abs_of_pos hr]
  simpa [hzero] using
    (hcont.continuousAt.tendsto (x := circleMap 0 r θ₀)).mono_left nhdsWithin_le_nhds

/-- Lemma IV.4-extra-4. For a fixed positive angular cutoff `η`, the contribution to the Poisson
integral coming from angles `θ` whose periodic angular distance from `θ₀` is greater than `η`
tends to `0` as `z` approaches the boundary point `circleMap 0 r θ₀` from within the open disk
`ball 0 r`. -/
theorem poisson_kernel_integral_away_from_boundary_angle_tendsto_zero
    {r θ₀ η : ℝ} (hr : 0 < r) (hη : 0 < η) :
    Tendsto
      (fun z : ℂ ↦
        (2 * Real.pi)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            indicator {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
              (fun θ : ℝ ↦ poissonKernel 0 z (circleMap 0 r θ)) θ)
      (nhdsWithin (circleMap 0 r θ₀) (ball (0 : ℂ) r))
      (nhds 0) := by
  by_cases hπη : Real.pi ≤ η
  · -- If the cutoff is at least `π`, there are no angles left to integrate over.
    simpa [cutoff_set_eq_empty_of_pi_le (θ₀ := θ₀) hπη] using
      (tendsto_const_nhds : Tendsto (fun _ : ℂ ↦ (0 : ℝ))
        (nhdsWithin (circleMap 0 r θ₀) (ball (0 : ℂ) r)) (nhds 0))
  · have hηπ : η < Real.pi := lt_of_not_ge hπη
    let m : ℝ := r * Real.sin (η / 2)
    have hm : 0 < m := by
      have hη_half_lt : η / 2 < Real.pi := by linarith
      have hsin_pos : 0 < Real.sin (η / 2) := by
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith) hη_half_lt
      exact mul_pos hr hsin_pos
    let boundary : ℂ := circleMap 0 r θ₀
    have hbound_eventually :
        ∀ᶠ z in nhdsWithin boundary (ball (0 : ℂ) r),
          ‖(2 * Real.pi)⁻¹ *
              ∫ θ in (0 : ℝ)..(2 * Real.pi),
                indicator {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
                  (fun θ : ℝ ↦ poissonKernel 0 z (circleMap 0 r θ)) θ‖
            ≤ (r ^ 2 - ‖z‖ ^ 2) / m ^ 2 := by
      -- Near the boundary point, reverse triangle turns the boundary separation into a uniform
      -- lower bound for the denominator with the interior point `z`.
      filter_upwards [inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ hm)] with z hz
      have hz_ball : z ∈ ball (0 : ℂ) r := hz.1
      have hz_close : ‖z - boundary‖ < m := by
        simpa [boundary, dist_eq_norm] using hz.2
      have hsep :
          ∀ θ : ℝ, η < |((θ - θ₀ : Real.Angle)).toReal| → m ≤ ‖circleMap 0 r θ - z‖ := by
        intro θ hcut
        have hboundary_gap :
            2 * m ≤ ‖circleMap 0 r θ - boundary‖ := by
          have hcut' : η ≤ |((θ - θ₀ : Real.Angle)).toReal| := le_of_lt hcut
          simpa [m, boundary, two_mul, mul_assoc, mul_left_comm, mul_comm] using
            away_arc_has_positive_distance
            (r := r) (θ₀ := θ₀) (η := η) (θ := θ) hr hη hηπ hcut'
        have htriangle :
            ‖circleMap 0 r θ - boundary‖ ≤ ‖circleMap 0 r θ - z‖ + ‖z - boundary‖ := by
          simpa [norm_sub_rev, add_comm, add_left_comm, add_assoc] using
            norm_sub_le_norm_sub_add_norm_sub (circleMap 0 r θ) z boundary
        linarith
      calc
        ‖(2 * Real.pi)⁻¹ *
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              indicator {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
                (fun θ : ℝ ↦ poissonKernel 0 z (circleMap 0 r θ)) θ‖
          = (2 * Real.pi)⁻¹ *
              ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
                  indicator {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
                    (fun θ : ℝ ↦ poissonKernel 0 z (circleMap 0 r θ)) θ‖ := by
              rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
        _ ≤ (2 * Real.pi)⁻¹ *
              (((r ^ 2 - ‖z‖ ^ 2) / m ^ 2) * |2 * Real.pi - 0|) := by
              gcongr
              exact intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ =>
                poisson_kernel_indicator_norm_le (r := r) (θ₀ := θ₀) (η := η)
                  (m := m) hz_ball hm hsep θ
        _ = (r ^ 2 - ‖z‖ ^ 2) / m ^ 2 := by
              rw [sub_zero, abs_of_pos Real.two_pi_pos]
              field_simp [show (2 * Real.pi : ℝ) ≠ 0 by positivity]
    have hradial :
        Tendsto (fun z : ℂ ↦ (r ^ 2 - ‖z‖ ^ 2) / m ^ 2)
          (nhdsWithin boundary (ball (0 : ℂ) r)) (nhds 0) := by
      -- Only the radial factor varies with `z`; the denominator constant is fixed.
      simpa [boundary, m, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (radial_gap_tendsto_zero (r := r) (θ₀ := θ₀) hr).const_mul ((m ^ 2)⁻¹)
    -- The integral is squeezed to zero by the uniform Poisson-kernel bound.
    exact squeeze_zero_norm' hbound_eventually hradial
