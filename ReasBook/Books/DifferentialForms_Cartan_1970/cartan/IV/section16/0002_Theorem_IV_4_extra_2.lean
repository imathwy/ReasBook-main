import DifferentialForms_Cartan_1970.cartan.IV.section16.«0003_Lemma_IV_4_extra_3»
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

-- Declarations for this item will be appended below by the statement pipeline.

open Complex Filter InnerProductSpace Metric Real Set Topology

-- Semantic search tool `lean_leansearch` is unavailable in this session; the statement surface was
-- checked against local section precedent and mathlib's harmonic-function files
-- `Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl` and
-- `Mathlib.Analysis.Complex.Harmonic.Poisson`.

/-- Helper for Theorem IV.4-extra-2: complexifying real boundary data preserves continuity on the
boundary circle. -/
lemma boundary_complexification_continuousOn {φ : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hφ : ContinuousOn φ (sphere c R)) :
    ContinuousOn (fun z ↦ (φ z : ℂ)) (sphere c R) := by
  -- Compose the boundary datum with the continuous embedding `ℝ → ℂ`.
  intro z hz
  exact Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt (hφ z hz)

/-- Helper for Theorem IV.4-extra-2: continuous boundary data on the circle is circle integrable
after complexification. -/
lemma boundary_complexification_circleIntegrable {φ : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hφ : ContinuousOn φ (sphere c R)) :
    CircleIntegrable (fun z ↦ (φ z : ℂ)) c R := by
  -- This is the regularity input needed by the Cauchy/Herglotz route.
  exact (boundary_complexification_continuousOn hφ).circleIntegrable hR.le

/-- Helper for Theorem IV.4-extra-2: the Poisson kernel has total mass `1` at every interior point
of the disc. -/
lemma poisson_circleAverage_const_one {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) :
    Real.circleAverage (poissonKernel c w • (fun _ : ℂ ↦ (1 : ℝ))) c R = 1 := by
  -- Apply the Poisson formula to the constant harmonic function `1`.
  simpa using
    (harmonicContOnCl_const (c := (1 : ℝ)) (s := ball c R)).circleAverage_poissonKernel_smul hw

/-- Helper for Theorem IV.4-extra-2: the complex Herglotz average along the boundary circle equals
twice the Cauchy transform minus the plain circle average. -/
lemma circleAverage_herglotzRieszKernel_mul_eq_two_cauchy_sub_average
    {Ψ : ℂ → ℂ} {c w : ℂ} {R : ℝ} (hR : 0 < R) (hΨ : ContinuousOn Ψ (sphere c R))
    (hw : w ∈ ball c R) :
    Real.circleAverage (fun z ↦ herglotzRieszKernel c w z * Ψ z) c R =
      (2 : ℂ) • (((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • Ψ z)) -
        Real.circleAverage Ψ c R := by
  have hsub_ne : ∀ z ∈ sphere c R, z - w ≠ 0 := by
    intro z hz hzw
    have hw_sphere : w ∈ sphere c R := by simpa [sub_eq_zero.mp hzw] using hz
    have hw_norm_lt : ‖w - c‖ < R := by simpa [mem_ball, dist_eq_norm] using hw
    have hw_norm_eq : ‖w - c‖ = R := by simpa [mem_sphere, dist_eq_norm] using hw_sphere
    exact (lt_irrefl R) (hw_norm_eq ▸ hw_norm_lt)
  have hratio_cont : ContinuousOn (fun z ↦ ((z - c) / (z - w)) • Ψ z) (sphere c R) := by
    -- The Cauchy factor is continuous on the boundary because the pole stays strictly inside.
    apply ContinuousOn.smul
    · apply ContinuousOn.div
      · exact continuousOn_id.sub continuousOn_const
      · exact continuousOn_id.sub continuousOn_const
      · intro z hz
        exact hsub_ne z hz
    · exact hΨ
  have hratio_int : CircleIntegrable (fun z ↦ ((z - c) / (z - w)) • Ψ z) c R :=
    hratio_cont.circleIntegrable hR.le
  have hΨ_int : CircleIntegrable Ψ c R := hΨ.circleIntegrable hR.le
  have hratio_eq :
      Real.circleAverage (fun z ↦ ((z - c) / (z - w)) • Ψ z) c R =
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • Ψ z) := by
    rw [Real.circleAverage_eq_circleIntegral (ne_of_lt hR).symm]
    apply congrArg (((2 * Real.pi * Complex.I : ℂ)⁻¹ • ·))
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hz_ne : z - c ≠ 0 := by
      intro hzc
      have hz_norm : ‖z - c‖ = R := by simpa [mem_sphere, dist_eq_norm] using hz
      have : ‖z - c‖ = 0 := by simp [hzc]
      linarith
    calc
      (z - c)⁻¹ • (((z - c) / (z - w)) • Ψ z)
          = (((z - c)⁻¹ * (z - c)) * (z - w)⁻¹) * Ψ z := by
              simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = (z - w)⁻¹ * Ψ z := by simp [hz_ne]
      _ = (z - w)⁻¹ • Ψ z := rfl
  calc
    Real.circleAverage (fun z ↦ herglotzRieszKernel c w z * Ψ z) c R =
        Real.circleAverage (fun z ↦ (2 : ℂ) • (((z - c) / (z - w)) • Ψ z) - Ψ z) c R := by
          -- Rewrite the Herglotz kernel on the boundary into the `2 * Cauchy - 1` form.
          apply circleAverage_congr_sphere
          intro z hz
          have hz' : z ∈ sphere c R := by simpa [abs_of_pos hR] using hz
          have hz_ne : z - w ≠ 0 := hsub_ne z hz'
          simp [herglotzRieszKernel_def]
          field_simp [hz_ne]
          ring
    _ = (2 : ℂ) • Real.circleAverage (fun z ↦ ((z - c) / (z - w)) • Ψ z) c R -
          Real.circleAverage Ψ c R := by
            -- Circle averages commute with scalar multiplication and subtraction.
            have hsubavg :=
              circleAverage_fun_sub
                (f₁ := fun z ↦ (2 : ℂ) • (((z - c) / (z - w)) • Ψ z))
                (f₂ := Ψ) ((ContinuousOn.const_smul hratio_cont (2 : ℂ)).circleIntegrable hR.le)
                hΨ_int
            rw [hsubavg]
            rw [circleAverage_fun_smul]
    _ = (2 : ℂ) • (((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • Ψ z)) -
          Real.circleAverage Ψ c R := by
            exact congrArg (fun t => (2 : ℂ) • t - Real.circleAverage Ψ c R) hratio_eq

/-- Helper for Theorem IV.4-extra-2: the Poisson integral of continuous boundary data is harmonic
throughout the open disc. -/
lemma poisson_circleAverage_harmonicOnNhd {φ : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R)) :
    HarmonicOnNhd (fun w ↦ Real.circleAverage (poissonKernel c w • φ) c R) (ball c R) := by
  let Ψ : ℂ → ℂ := fun z ↦ (φ z : ℂ)
  have hΨ : ContinuousOn Ψ (sphere c R) := boundary_complexification_continuousOn hφ
  have hΨ_int : CircleIntegrable Ψ c R := boundary_complexification_circleIntegrable hR hφ
  let G : ℂ → ℂ := fun w ↦ ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • Ψ z)
  let K : ℂ → ℂ := fun _ ↦ Real.circleAverage Ψ c R
  let F : ℂ → ℂ := (2 : ℂ) • G - K
  have hF_analytic : AnalyticOnNhd ℂ F (ball c R) := by
    -- The Cauchy transform is analytic on the open disc, and affine operations preserve that.
    have hG_analytic : AnalyticOnNhd ℂ G (ball c R) := by
      simpa [G] using
        (hasFPowerSeriesOn_cauchy_integral (R := ⟨R, hR.le⟩) (by simpa using hΨ_int)
          (by simpa using hR)).analyticOnNhd
    simpa [F] using
      (hG_analytic.const_smul (c := (2 : ℂ))).sub
        (show AnalyticOnNhd ℂ K (ball c R) by simpa [K] using
          (analyticOnNhd_const (v := Real.circleAverage Ψ c R)))
  have hEq :
      EqOn (fun w ↦ Real.circleAverage (poissonKernel c w • φ) c R)
        (fun w ↦ (F w).re) (ball c R) := by
    intro w hw
    have hker_cont : ContinuousOn (fun z ↦ herglotzRieszKernel c w z * Ψ z) (sphere c R) := by
      -- The boundary integrand is continuous because the Herglotz pole stays off the circle.
      rw [herglotzRieszKernel_fun_def]
      apply ContinuousOn.mul
      · apply ContinuousOn.div
        · exact (continuousOn_id.sub continuousOn_const).add continuousOn_const
        · exact (continuousOn_id.sub continuousOn_const).sub continuousOn_const
        · intro z hz
          have hz_ne : z - w ≠ 0 := by
            intro hzw
            have hw_sphere : w ∈ sphere c R := by simpa [sub_eq_zero.mp hzw] using hz
            have hw_norm_lt : ‖w - c‖ < R := by simpa [mem_ball, dist_eq_norm] using hw
            have hw_norm_eq : ‖w - c‖ = R := by simpa [mem_sphere, dist_eq_norm] using hw_sphere
            exact (lt_irrefl R) (hw_norm_eq ▸ hw_norm_lt)
          have hz_eq : (z - c) - (w - c) = z - w := by ring
          rw [hz_eq]
          exact hz_ne
      · exact hΨ
    have hker_int : CircleIntegrable (fun z ↦ herglotzRieszKernel c w z * Ψ z) c R :=
      hker_cont.circleIntegrable hR.le
    have hRe_eq :
        EqOn (poissonKernel c w • φ)
          (Complex.reCLM ∘ fun z ↦ herglotzRieszKernel c w z * Ψ z) (sphere c R) := by
      -- The Poisson kernel is the real part of the Herglotz kernel on the boundary circle.
      intro z hz
      simp [Ψ, poissonKernel_eq_re_herglotzRieszKernel, Complex.mul_re]
    calc
      Real.circleAverage (poissonKernel c w • φ) c R =
          Real.circleAverage (Complex.reCLM ∘ fun z ↦ herglotzRieszKernel c w z * Ψ z) c R := by
            apply circleAverage_congr_sphere
            intro z hz
            have hz' : z ∈ sphere c R := by simpa [abs_of_pos hR] using hz
            exact hRe_eq hz'
      _ = (Real.circleAverage (fun z ↦ herglotzRieszKernel c w z * Ψ z) c R).re := by
            simpa using Complex.reCLM.circleAverage_comp_comm hker_int
      _ = (F w).re := by
            simpa [F, G, K] using
              congrArg Complex.re
                (circleAverage_herglotzRieszKernel_mul_eq_two_cauchy_sub_average hR hΨ hw)
  intro w hw
  have hEq_nhds := hEq.eventuallyEq_of_mem (isOpen_ball.mem_nhds hw)
  -- Replace the Poisson average by the real part of the analytic Cauchy transform near `w`.
  exact (harmonicAt_congr_nhds hEq_nhds).2 <| (hF_analytic w hw).harmonicAt_re

/-- Helper for Theorem IV.4-extra-2: if the angular cutoff is at least `π`, then the excluded-angle
set is empty because every angle representative lies in `[-π, π]`. -/
lemma cutoff_set_eq_empty_of_pi_le_local {θ₀ η : ℝ} (hπη : Real.pi ≤ η) :
    {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|} = ∅ := by
  -- The periodic-angle representative is always bounded in absolute value by `π`.
  ext θ
  simp [not_lt.mpr <| (Real.Angle.abs_toReal_le_pi _).trans hπη]

/-- Helper for Theorem IV.4-extra-2: the chord length on the radius-`r` circle is controlled by the
representative of the angular difference. -/
lemma circle_distance_eq_two_mul_sin_half_toReal_local
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
  -- Rewrite one point by the canonical angle representative and then factor the chord.
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

/-- Helper for Theorem IV.4-extra-2: staying `η` away from a boundary angle gives a uniform lower
bound on the corresponding chord length. -/
lemma away_arc_has_positive_distance_local
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
  -- Convert the angular lower bound into a metric lower bound through the chord formula.
  calc
    2 * r * Real.sin (η / 2) ≤ 2 * r * |Real.sin (δ / 2)| := by
      rw [hsin_abs]
      gcongr
    _ = ‖circleMap 0 r θ - circleMap 0 r θ₀‖ := by
      simpa [δ] using
        (circle_distance_eq_two_mul_sin_half_toReal_local (θ := θ) (θ₀ := θ₀) hr).symm

/-- Helper for Theorem IV.4-extra-2: on a cutoff arc where the denominator stays at least `m`, the
truncated Poisson kernel is uniformly bounded by `(r^2 - ‖z‖^2) / m^2`. -/
lemma poisson_kernel_indicator_norm_le_local
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
    -- On the cutoff arc, the indicator keeps the kernel and the denominator bound applies.
    simp [hcut]
    simpa [Real.norm_eq_abs, poissonKernel_def, sub_zero, norm_circleMap_zero, abs_of_pos hr,
      sub_eq_add_neg, sq] using
      (show
        |(‖circleMap 0 r θ - (0 : ℂ)‖ ^ 2 - ‖z - 0‖ ^ 2) /
            ‖(circleMap 0 r θ - 0) - (z - 0)‖ ^ 2| ≤ (r ^ 2 - ‖z‖ ^ 2) / m ^ 2 from by
          exact (abs_of_nonneg hkernel_nonneg).symm ▸ hkernel_le)
  · -- Outside the cutoff arc, the indicator forces the integrand to vanish.
    simp [hcut, hnum_nonneg, div_nonneg, hm.le]

/-- Helper for Theorem IV.4-extra-2: the radial factor in the centered Poisson kernel vanishes as
the interior point approaches the boundary. -/
lemma radial_gap_tendsto_zero_local {r θ₀ : ℝ} (hr : 0 < r) :
    Tendsto (fun z : ℂ ↦ r ^ 2 - ‖z‖ ^ 2)
      (nhdsWithin (circleMap 0 r θ₀) (ball (0 : ℂ) r)) (nhds 0) := by
  have hcont : Continuous fun z : ℂ ↦ r ^ 2 - ‖z‖ ^ 2 := by
    fun_prop
  have hzero : r ^ 2 - ‖circleMap 0 r θ₀‖ ^ 2 = 0 := by
    simp [norm_circleMap_zero, abs_of_pos hr]
  -- The boundary point lies exactly at radius `r`, so the radial defect tends to zero.
  simpa [hzero] using
    (hcont.continuousAt.tendsto (x := circleMap 0 r θ₀)).mono_left nhdsWithin_le_nhds

/-- Helper for Theorem IV.4-extra-2: if the pole stays strictly inside the centered circle, then
the Poisson kernel is continuous along that boundary circle. -/
lemma poissonKernel_continuousOn_sphere_of_mem_ball_local {z : ℂ} {r : ℝ}
    (hz : z ∈ Metric.ball (0 : ℂ) r) :
    ContinuousOn (poissonKernel 0 z) (Metric.sphere (0 : ℂ) r) := by
  -- The denominator never vanishes on the boundary because the interior pole does not meet it.
  have h_num :
      ContinuousOn (fun x : ℂ ↦ ‖x - 0‖ ^ 2 - ‖z - 0‖ ^ 2) (Metric.sphere (0 : ℂ) r) := by
    exact ((continuousOn_id.sub continuousOn_const).norm.pow 2).sub continuousOn_const
  have h_den :
      ContinuousOn (fun x : ℂ ↦ ‖(x - 0) - (z - 0)‖ ^ 2) (Metric.sphere (0 : ℂ) r) := by
    exact (((continuousOn_id.sub continuousOn_const).sub continuousOn_const).norm.pow 2)
  refine ContinuousOn.div h_num h_den ?_
  intro x hx
  have hx_ne : x ≠ z := by
    intro hxz
    have : ‖z - 0‖ = r := by simpa [hxz] using hx
    exact (mem_ball_iff_norm.mp hz).ne this
  have hsub_eq : (x - 0) - (z - 0) = x - z := by ring
  have hdiff : (x - 0) - (z - 0) ≠ 0 := by
    rw [hsub_eq]
    exact sub_ne_zero.mpr hx_ne
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hdiff)

/-- Helper for Theorem IV.4-extra-2: for a fixed positive angular cutoff `η`, the contribution of
angles staying `η` away from `θ₀` to the centered Poisson integral tends to `0` at the boundary. -/
theorem poisson_kernel_integral_away_from_boundary_angle_tendsto_zero_local
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
  · -- If the cutoff dominates `π`, the truncated set is empty and the integral is identically zero.
    simpa [cutoff_set_eq_empty_of_pi_le_local (θ₀ := θ₀) hπη] using
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
      -- Close enough to the boundary point, reverse triangle gives a uniform denominator bound.
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
            away_arc_has_positive_distance_local
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
                poisson_kernel_indicator_norm_le_local
                  (r := r) (θ₀ := θ₀) (η := η) (m := m) hz_ball hm hsep θ
        _ = (r ^ 2 - ‖z‖ ^ 2) / m ^ 2 := by
              rw [sub_zero, abs_of_pos Real.two_pi_pos]
              field_simp [show (2 * Real.pi : ℝ) ≠ 0 by positivity]
    have hradial :
        Tendsto (fun z : ℂ ↦ (r ^ 2 - ‖z‖ ^ 2) / m ^ 2)
          (nhdsWithin boundary (ball (0 : ℂ) r)) (nhds 0) := by
      -- The only varying factor is the radial defect; the cutoff denominator is constant.
      simpa [boundary, m, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (radial_gap_tendsto_zero_local (r := r) (θ₀ := θ₀) hr).const_mul ((m ^ 2)⁻¹)
    -- Squeeze the truncated integral to zero using the uniform kernel bound.
    exact squeeze_zero_norm' hbound_eventually hradial

/-- Helper for Theorem IV.4-extra-2: translating the disc to the origin turns the Poisson average
minus the boundary value into a centered Poisson average of the translated boundary error. -/
lemma poisson_circleAverage_translate_sub_boundary_value
    {φ : ℂ → ℝ} {c z : ℂ} {R θ₀ : ℝ} (hφ : ContinuousOn φ (sphere c R))
    (hz : z ∈ ball c R) :
    Real.circleAverage (poissonKernel c z • φ) c R - φ (circleMap c R θ₀) =
      Real.circleAverage
        (poissonKernel 0 (z - c) •
          fun w ↦ φ (w + c) - φ (circleMap c R θ₀)) 0 R := by
  let ψ : ℂ → ℝ := fun w ↦ φ (w + c)
  have hz0 : z - c ∈ ball (0 : ℂ) R := by
    simpa [mem_ball, dist_eq_norm] using hz
  have hψ_cont : ContinuousOn ψ (sphere (0 : ℂ) R) := by
    -- The translated boundary datum is continuous because addition by `c` maps the centered sphere
    -- onto the original boundary circle.
    refine hφ.comp' (by fun_prop) ?_
    intro w hw
    simpa [mem_sphere, dist_eq_norm] using hw
  have hkernel_cont : ContinuousOn (poissonKernel 0 (z - c)) (sphere (0 : ℂ) R) :=
    poissonKernel_continuousOn_sphere_of_mem_ball_local hz0
  have hRpos : 0 < R := pos_of_mem_ball hz0
  have hkernel_cont_abs : ContinuousOn (poissonKernel 0 (z - c)) (sphere (0 : ℂ) |R|) := by
    simpa [abs_of_pos hRpos] using hkernel_cont
  have hψ_int : CircleIntegrable ψ 0 R := hψ_cont.circleIntegrable (le_of_lt <| pos_of_mem_ball hz0)
  have hconst_int : CircleIntegrable (fun _ : ℂ ↦ φ (circleMap c R θ₀)) 0 R :=
    continuousOn_const.circleIntegrable (le_of_lt <| pos_of_mem_ball hz0)
  have hpoissonψ_int :
      CircleIntegrable (poissonKernel 0 (z - c) • ψ) 0 R := by
    exact hψ_int.smul_of_continuousOn hkernel_cont_abs
  have hpoisson_const_int :
      CircleIntegrable
        (poissonKernel 0 (z - c) • (fun _ : ℂ ↦ φ (circleMap c R θ₀))) 0 R := by
    exact hconst_int.smul_of_continuousOn hkernel_cont_abs
  have htranslate :
      Real.circleAverage (poissonKernel c z • φ) c R =
        Real.circleAverage (poissonKernel 0 (z - c) • ψ) 0 R := by
    rw [← circleAverage_map_add_const (f := poissonKernel c z • φ) (c := c) (R := R)]
    apply circleAverage_congr_sphere
    intro w hw
    simp [ψ, poissonKernel_def]
  have hone :
      Real.circleAverage (poissonKernel 0 (z - c) • (fun _ : ℂ ↦ (1 : ℝ))) 0 R = 1 :=
    poisson_circleAverage_const_one hz0
  have hconst :
      Real.circleAverage
          (poissonKernel 0 (z - c) • (fun _ : ℂ ↦ φ (circleMap c R θ₀))) 0 R
        = φ (circleMap c R θ₀) := by
    let φ₀ : ℝ := φ (circleMap c R θ₀)
    have hcongr :
        (poissonKernel 0 (z - c) • (fun _ : ℂ ↦ φ₀)) =
          fun w ↦ φ₀ • ((poissonKernel 0 (z - c) • (fun _ : ℂ ↦ (1 : ℝ))) w) := by
      funext w
      simp [smul_eq_mul, mul_comm]
    calc
      Real.circleAverage
          (poissonKernel 0 (z - c) • (fun _ : ℂ ↦ φ₀)) 0 R
        = φ₀ • Real.circleAverage (poissonKernel 0 (z - c) • (fun _ : ℂ ↦ (1 : ℝ))) 0 R := by
            rw [hcongr, Real.circleAverage_fun_smul]
      _ = φ₀ := by
          rw [hone]
          simp [smul_eq_mul]
  -- Subtract the constant boundary value by converting it into the Poisson average of a constant.
  calc
    Real.circleAverage (poissonKernel c z • φ) c R - φ (circleMap c R θ₀)
      = Real.circleAverage (poissonKernel 0 (z - c) • ψ) 0 R
          - Real.circleAverage
              (poissonKernel 0 (z - c) • (fun _ : ℂ ↦ φ (circleMap c R θ₀))) 0 R := by
            rw [htranslate, hconst]
    _ = Real.circleAverage
          ((poissonKernel 0 (z - c) • ψ) -
            (poissonKernel 0 (z - c) • (fun _ : ℂ ↦ φ (circleMap c R θ₀)))) 0 R := by
          simpa [Pi.sub_apply] using
            (Real.circleAverage_fun_sub hpoissonψ_int hpoisson_const_int).symm
    _ = Real.circleAverage
          (poissonKernel 0 (z - c) •
            fun w ↦ φ (w + c) - φ (circleMap c R θ₀)) 0 R := by
          change
            Real.circleAverage
              (fun z_1 ↦
                (poissonKernel 0 (z - c) • ψ) z_1 -
                  (poissonKernel 0 (z - c) • (fun _ : ℂ ↦ φ (circleMap c R θ₀))) z_1) 0 R =
            _
          apply circleAverage_congr_sphere
          intro w hw
          simp [ψ, smul_eq_mul]
          ring

/-- Helper for Theorem IV.4-extra-2: continuity of the boundary datum along the circle parameter
turns small angular gaps into small boundary oscillation. -/
lemma boundary_value_oscillation_small_of_angle_gap
    {φ : ℂ → ℝ} {c : ℂ} {R θ₀ ε : ℝ} (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R))
    (hε : 0 < ε) :
    ∃ η, 0 < η ∧ η < Real.pi ∧
      ∀ θ : ℝ, |((θ - θ₀ : Real.Angle)).toReal| ≤ η →
        |φ (circleMap c R θ) - φ (circleMap c R θ₀)| ≤ ε := by
  let g : ℝ → ℝ := fun θ ↦ φ (circleMap c R θ)
  have hg_contOn : ContinuousOn g Set.univ := by
    -- Compose the boundary datum with the circle parametrization.
    refine hφ.comp' (by simpa [g] using continuous_circleMap c R) ?_
    intro θ hθ
    simpa [g, abs_of_pos hR] using circleMap_mem_sphere c hR.le θ
  have hg_contAt : ContinuousAt g θ₀ := by
    simpa [continuousWithinAt_univ] using hg_contOn θ₀ (by simp)
  rcases Metric.continuousAt_iff.1 hg_contAt ε hε with ⟨δ, hδ_pos, hδ⟩
  refine ⟨min (δ / 2) (Real.pi / 2), by positivity, ?_, ?_⟩
  · have hmin_le : min (δ / 2) (Real.pi / 2) ≤ Real.pi / 2 := min_le_right _ _
    linarith [Real.pi_pos]
  · intro θ hθ
    let δθ : ℝ := ((θ - θ₀ : Real.Angle)).toReal
    have hδθ_angle : ((δθ : ℝ) : Real.Angle) = (θ - θ₀ : Real.Angle) := by
      simp [δθ]
    have hsum : ((δθ + θ₀ : ℝ) : Real.Angle) = (θ : Real.Angle) := by
      have := congrArg (fun x : Real.Angle => x + (θ₀ : Real.Angle)) hδθ_angle
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    have hcircle : circleMap c R (δθ + θ₀) = circleMap c R θ := by
      rw [circleMap_eq_circleMap_iff c hR.ne']
      rcases (Real.Angle.angle_eq_iff_two_pi_dvd_sub).mp hsum with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hk' : δθ + θ₀ = θ + (k : ℝ) * (2 * Real.pi) := by
        linarith
      simpa [add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm] using
        congrArg (fun t : ℝ => t * Complex.I) hk'
    have hδθ_lt : |δθ| < δ := by
      have hη_lt : min (δ / 2) (Real.pi / 2) < δ := by
        have hleft : min (δ / 2) (Real.pi / 2) ≤ δ / 2 := min_le_left _ _
        linarith
      exact lt_of_le_of_lt hθ hη_lt
    have hclose : dist (δθ + θ₀) θ₀ < δ := by
      simpa [Real.dist_eq, δθ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hδθ_lt
    have hvalue_lt :
        |φ (circleMap c R (δθ + θ₀)) - φ (circleMap c R θ₀)| < ε := by
      simpa [g, Real.dist_eq, sub_eq_add_neg] using (hδ hclose)
    -- Replace `θ` by the canonical nearby representative `θ₀ + δθ`.
    simpa [hcircle] using le_of_lt hvalue_lt

/-- Helper for Theorem IV.4-extra-2: the complement of the closed near-arc cutoff is the open
far-arc cutoff used in the Poisson approximate-identity split. -/
lemma poisson_translated_near_compl_eq_far {θ₀ η : ℝ} :
    {θ : ℝ | |((θ - θ₀ : Real.Angle)).toReal| ≤ η}ᶜ =
      {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|} := by
  -- The complementary cutoff just reverses `≤ η` into the strict inequality `η < _`.
  ext θ
  simp [not_le]

/-- Helper for Theorem IV.4-extra-2: the translated Poisson error splits pointwise into its near-
arc and far-arc indicator pieces. -/
lemma poisson_translated_error_pointwise_split_near_far
    {φ : ℂ → ℝ} {c z : ℂ} {R θ₀ η : ℝ} :
    let full : ℝ → ℝ := fun θ ↦
      poissonKernel 0 (z - c) (circleMap 0 R θ) *
        (φ (circleMap c R θ) - φ (circleMap c R θ₀))
    full =
      indicator {θ : ℝ | |((θ - θ₀ : Real.Angle)).toReal| ≤ η} full +
        indicator {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|} full := by
  let near : Set ℝ := {θ : ℝ | |((θ - θ₀ : Real.Angle)).toReal| ≤ η}
  let far : Set ℝ := {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
  let full : ℝ → ℝ := fun θ ↦
    poissonKernel 0 (z - c) (circleMap 0 R θ) *
      (φ (circleMap c R θ) - φ (circleMap c R θ₀))
  have hfar_compl : nearᶜ = far := poisson_translated_near_compl_eq_far (θ₀ := θ₀) (η := η)
  -- Evaluate the canonical indicator partition at each angle and rewrite the complement as `far`.
  funext θ
  simpa [near, far, full, hfar_compl] using
    (congrArg (fun f : ℝ → ℝ => f θ) (Set.indicator_self_add_compl near full)).symm

/-- Helper for Theorem IV.4-extra-2: once the translated near and far cutoff pieces are known to be
interval integrable, the full translated Poisson error average is bounded by the sum of their
interval averages. -/
lemma poisson_translated_error_split_near_far_interval
    {φ : ℂ → ℝ} {c z : ℂ} {R θ₀ η : ℝ}
    (hnear :
      IntervalIntegrable
        (indicator {θ : ℝ | |((θ - θ₀ : Real.Angle)).toReal| ≤ η}
          (fun θ : ℝ ↦
            poissonKernel 0 (z - c) (circleMap 0 R θ) *
              (φ (circleMap c R θ) - φ (circleMap c R θ₀)))) MeasureTheory.volume 0
        (2 * Real.pi))
    (hfar :
      IntervalIntegrable
        (indicator {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
          (fun θ : ℝ ↦
            poissonKernel 0 (z - c) (circleMap 0 R θ) *
              (φ (circleMap c R θ) - φ (circleMap c R θ₀)))) MeasureTheory.volume 0
        (2 * Real.pi)) :
    |(2 * Real.pi)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          poissonKernel 0 (z - c) (circleMap 0 R θ) * (φ (circleMap c R θ) - φ (circleMap c R θ₀))
            ∂MeasureTheory.volume|
      ≤
        |(2 * Real.pi)⁻¹ *
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              indicator {θ : ℝ | |((θ - θ₀ : Real.Angle)).toReal| ≤ η}
                (fun θ : ℝ ↦
                  poissonKernel 0 (z - c) (circleMap 0 R θ) *
                    (φ (circleMap c R θ) - φ (circleMap c R θ₀))) θ ∂MeasureTheory.volume|
          +
            |(2 * Real.pi)⁻¹ *
              ∫ θ in (0 : ℝ)..(2 * Real.pi),
                indicator {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
                  (fun θ : ℝ ↦
                    poissonKernel 0 (z - c) (circleMap 0 R θ) *
                      (φ (circleMap c R θ) - φ (circleMap c R θ₀))) θ ∂MeasureTheory.volume| := by
  let full : ℝ → ℝ := fun θ ↦
    poissonKernel 0 (z - c) (circleMap 0 R θ) * (φ (circleMap c R θ) - φ (circleMap c R θ₀))
  let near : Set ℝ := {θ : ℝ | |((θ - θ₀ : Real.Angle)).toReal| ≤ η}
  let far : Set ℝ := {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
  have hsplit : full = indicator near full + indicator far full := by
    -- Package the pointwise cutoff partition as an equality of functions.
    simpa [full, near, far] using
      (poisson_translated_error_pointwise_split_near_far
        (φ := φ) (c := c) (z := z) (R := R) (θ₀ := θ₀) (η := η))
  have hsplit_eval :
      ∀ θ : ℝ, full θ = indicator near full θ + indicator far full θ := by
    intro θ
    exact congrFun hsplit θ
  have hnear' : IntervalIntegrable (indicator near full) MeasureTheory.volume 0 (2 * Real.pi) := by
    simpa [near, full] using hnear
  have hfar' : IntervalIntegrable (indicator far full) MeasureTheory.volume 0 (2 * Real.pi) := by
    simpa [far, full] using hfar
  have hintegral :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), full θ ∂MeasureTheory.volume) =
        (∫ θ in (0 : ℝ)..(2 * Real.pi), indicator near full θ ∂MeasureTheory.volume) +
          ∫ θ in (0 : ℝ)..(2 * Real.pi), indicator far full θ ∂MeasureTheory.volume := by
    -- Integrate the near/far partition termwise over the whole interval.
    calc
      (∫ θ in (0 : ℝ)..(2 * Real.pi), full θ ∂MeasureTheory.volume) =
          ∫ θ in (0 : ℝ)..(2 * Real.pi), (indicator near full θ + indicator far full θ)
            ∂MeasureTheory.volume := by
            apply intervalIntegral.integral_congr_ae
            exact Filter.Eventually.of_forall fun θ _ ↦ hsplit_eval θ
      _ = (∫ θ in (0 : ℝ)..(2 * Real.pi), indicator near full θ ∂MeasureTheory.volume) +
            ∫ θ in (0 : ℝ)..(2 * Real.pi), indicator far full θ ∂MeasureTheory.volume := by
            simpa using intervalIntegral.integral_add hnear' hfar'
  let nearIntegral : ℝ :=
    ∫ θ in (0 : ℝ)..(2 * Real.pi), indicator near full θ ∂MeasureTheory.volume
  let farIntegral : ℝ :=
    ∫ θ in (0 : ℝ)..(2 * Real.pi), indicator far full θ ∂MeasureTheory.volume
  have hmul :
      (2 * Real.pi)⁻¹ * (nearIntegral + farIntegral) =
        (2 * Real.pi)⁻¹ * nearIntegral + (2 * Real.pi)⁻¹ * farIntegral := by
    ring
  -- After rewriting the full error as the sum of the near and far pieces, `abs_add` finishes.
  calc
    |(2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), full θ ∂MeasureTheory.volume|
      = |(2 * Real.pi)⁻¹ * (nearIntegral + farIntegral)| := by
          simpa [nearIntegral, farIntegral] using
            congrArg (fun t : ℝ ↦ |(2 * Real.pi)⁻¹ * t|) hintegral
    _ =
        |((2 * Real.pi)⁻¹ * nearIntegral) + ((2 * Real.pi)⁻¹ * farIntegral)| := by
          rw [hmul]
    _ ≤
        |(2 * Real.pi)⁻¹ * nearIntegral| + |(2 * Real.pi)⁻¹ * farIntegral| := by
          simpa [nearIntegral, farIntegral, Real.norm_eq_abs] using
            (norm_add_le ((2 * Real.pi)⁻¹ * nearIntegral) ((2 * Real.pi)⁻¹ * farIntegral))

/-- Helper for Theorem IV.4-extra-2: continuity of the boundary datum on the circle gives a
uniform bound for its difference from the chosen boundary value on the compact angle interval. -/
lemma boundary_difference_bounded_on_circle_interval
    {φ : ℂ → ℝ} {c : ℂ} {R θ₀ : ℝ} (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R)) :
    ∃ M, 0 ≤ M ∧
      ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
        |φ (circleMap c R θ) - φ (circleMap c R θ₀)| ≤ M := by
  let g : ℝ → ℝ := fun θ ↦ |φ (circleMap c R θ) - φ (circleMap c R θ₀)|
  have hcircle_cont : ContinuousOn (fun θ : ℝ ↦ φ (circleMap c R θ)) Set.univ := by
    -- Parametrize the boundary circle by `circleMap`.
    refine hφ.comp' (by simpa using continuous_circleMap c R) ?_
    intro θ hθ
    simpa [abs_of_pos hR] using circleMap_mem_sphere c hR.le θ
  have hg_cont : ContinuousOn g (Set.Icc 0 (2 * Real.pi)) := by
    -- The absolute boundary difference is continuous on the compact interval of angles.
    refine ((hcircle_cont.sub continuousOn_const).abs).mono ?_
    intro θ hθ
    simp
  rcases
      (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi))).exists_bound_of_continuousOn
        hg_cont with
    ⟨M, hM⟩
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro θ hθ
  -- Replace the norm bound by an absolute-value bound and enlarge the constant to be nonnegative.
  calc
    |φ (circleMap c R θ) - φ (circleMap c R θ₀)|
      = ‖g θ‖ := by simp [g]
    _ ≤ M := hM θ hθ
    _ ≤ max M 0 := le_max_left _ _

/-- Helper for Theorem IV.4-extra-2: when `η < π`, the closed angle cutoff
`{|θ.toReal| ≤ η}` is closed in `Real.Angle`. -/
lemma isClosed_angle_abs_toReal_le_local {η : ℝ} (hηπ : η < Real.pi) :
    IsClosed {θ : Real.Angle | |θ.toReal| ≤ η} := by
  have himage :
      {θ : Real.Angle | |θ.toReal| ≤ η} = ((↑) : ℝ → Real.Angle) '' Set.Icc (-η) η := by
    ext θ
    constructor
    · intro hθ
      -- The canonical real representative of the angle already lies in `[-η, η]`.
      refine ⟨θ.toReal, abs_le.mp hθ, Real.Angle.coe_toReal θ⟩
    · rintro ⟨x, hx, rfl⟩
      have hx_mem : x ∈ Set.Ioc (-Real.pi) Real.pi := by
        constructor
        · have hlt : -Real.pi < -η := by linarith
          exact lt_of_lt_of_le hlt hx.1
        · exact hx.2.trans hηπ.le
      have hto : ((x : Real.Angle).toReal) = x :=
        Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.2 hx_mem
      -- On the principal branch, `toReal` is the identity, so the interval bound becomes `abs ≤ η`.
      simpa [hto] using (abs_le.mpr hx)
  rw [himage]
  exact (isCompact_Icc.image Real.Angle.continuous_coe).isClosed

/-- Helper for Theorem IV.4-extra-2: the near-angle cutoff is measurable on the angle parameter
interval once the cutoff lies below `π`. -/
lemma measurableSet_translated_near_arc_local {θ₀ η : ℝ} (hηπ : η < Real.pi) :
    MeasurableSet {θ : ℝ | |((θ - θ₀ : Real.Angle)).toReal| ≤ η} := by
  let f : ℝ → Real.Angle := fun θ ↦ (θ - θ₀ : Real.Angle)
  have hclosed : IsClosed {θ : Real.Angle | |θ.toReal| ≤ η} :=
    isClosed_angle_abs_toReal_le_local hηπ
  have hcont : Continuous f := Real.Angle.continuous_coe.comp (continuous_id.sub continuous_const)
  -- The cutoff is the preimage of the closed angle ball under a continuous map.
  simpa [f] using (hclosed.preimage hcont).measurableSet

/-- Helper for Theorem IV.4-extra-2: the complementary far-angle cutoff is measurable on the angle
parameter interval. -/
lemma measurableSet_translated_far_arc_local {θ₀ η : ℝ} (hηπ : η < Real.pi) :
    MeasurableSet {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|} := by
  -- Rewrite the far cutoff as the complement of the measurable near cutoff.
  rw [← poisson_translated_near_compl_eq_far (θ₀ := θ₀) (η := η)]
  exact (measurableSet_translated_near_arc_local (θ₀ := θ₀) hηπ).compl

/-- Helper for Theorem IV.4-extra-2: the translated Poisson error integrand is continuous on the
compact angle interval. -/
lemma translated_error_continuousOn_Icc_local
    {φ : ℂ → ℝ} {c z : ℂ} {R θ₀ : ℝ} (hz : z ∈ ball c R)
    (hφ : ContinuousOn φ (sphere c R)) :
    ContinuousOn
      (fun θ : ℝ ↦
        poissonKernel 0 (z - c) (circleMap 0 R θ) *
          (φ (circleMap c R θ) - φ (circleMap c R θ₀)))
      (Set.Icc 0 (2 * Real.pi)) := by
  have hz0 : z - c ∈ ball (0 : ℂ) R := by
    simpa [mem_ball, dist_eq_norm] using hz
  have hR : 0 < R := pos_of_mem_ball hz0
  have hkernel :
      ContinuousOn (fun θ : ℝ ↦ poissonKernel 0 (z - c) (circleMap 0 R θ))
        (Set.Icc 0 (2 * Real.pi)) := by
    -- The centered Poisson kernel is continuous along the boundary circle.
    refine (poissonKernel_continuousOn_sphere_of_mem_ball_local hz0).comp'
      (continuous_circleMap 0 R).continuousOn ?_
    intro θ hθ
    simpa [abs_of_pos hR] using circleMap_mem_sphere (0 : ℂ) hR.le θ
  have hboundary :
      ContinuousOn (fun θ : ℝ ↦ φ (circleMap c R θ)) (Set.Icc 0 (2 * Real.pi)) := by
    -- The boundary datum becomes continuous after parametrizing the circle.
    refine hφ.comp' (continuous_circleMap c R).continuousOn ?_
    intro θ hθ
    simpa [abs_of_pos hR] using circleMap_mem_sphere c hR.le θ
  -- Multiply the continuous kernel by the continuous boundary difference.
  exact hkernel.mul (hboundary.sub continuousOn_const)

/-- Helper for Theorem IV.4-extra-2: the near-cutoff translated Poisson error is interval
integrable on `0 .. 2π`. -/
lemma translated_near_arc_intervalIntegrable_local
    {φ : ℂ → ℝ} {c z : ℂ} {R θ₀ η : ℝ} (hz : z ∈ ball c R)
    (hφ : ContinuousOn φ (sphere c R)) (hηπ : η < Real.pi) :
    IntervalIntegrable
      (indicator {θ : ℝ | |((θ - θ₀ : Real.Angle)).toReal| ≤ η}
        (fun θ : ℝ ↦
          poissonKernel 0 (z - c) (circleMap 0 R θ) *
            (φ (circleMap c R θ) - φ (circleMap c R θ₀))))
      MeasureTheory.volume 0 (2 * Real.pi) := by
  have hfull :
      MeasureTheory.IntegrableOn
        (fun θ : ℝ ↦
          poissonKernel 0 (z - c) (circleMap 0 R θ) *
            (φ (circleMap c R θ) - φ (circleMap c R θ₀)))
        (Set.Icc 0 (2 * Real.pi)) := by
    exact ContinuousOn.integrableOn_Icc <|
      translated_error_continuousOn_Icc_local (c := c) (z := z) (R := R) (θ₀ := θ₀) hz hφ
  -- The cutoff preserves integrability because the near-arc set is measurable.
  refine (intervalIntegrable_iff_integrableOn_Icc_of_le Real.two_pi_pos.le).2 ?_
  exact hfull.indicator (measurableSet_translated_near_arc_local (θ₀ := θ₀) hηπ)

/-- Helper for Theorem IV.4-extra-2: the far-cutoff translated Poisson error is interval
integrable on `0 .. 2π`. -/
lemma translated_far_arc_intervalIntegrable_local
    {φ : ℂ → ℝ} {c z : ℂ} {R θ₀ η : ℝ} (hz : z ∈ ball c R)
    (hφ : ContinuousOn φ (sphere c R)) (hηπ : η < Real.pi) :
    IntervalIntegrable
      (indicator {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
        (fun θ : ℝ ↦
          poissonKernel 0 (z - c) (circleMap 0 R θ) *
            (φ (circleMap c R θ) - φ (circleMap c R θ₀))))
      MeasureTheory.volume 0 (2 * Real.pi) := by
  have hfull :
      MeasureTheory.IntegrableOn
        (fun θ : ℝ ↦
          poissonKernel 0 (z - c) (circleMap 0 R θ) *
            (φ (circleMap c R θ) - φ (circleMap c R θ₀)))
        (Set.Icc 0 (2 * Real.pi)) := by
    exact ContinuousOn.integrableOn_Icc <|
      translated_error_continuousOn_Icc_local (c := c) (z := z) (R := R) (θ₀ := θ₀) hz hφ
  -- The far-arc indicator is measurable as the complement of the near-arc cutoff.
  refine (intervalIntegrable_iff_integrableOn_Icc_of_le Real.two_pi_pos.le).2 ?_
  exact hfull.indicator (measurableSet_translated_far_arc_local (θ₀ := θ₀) hηπ)

/-- Helper for Theorem IV.4-extra-2: the centered Poisson kernel is nonnegative on the boundary
circle whenever the pole lies strictly inside the disc. -/
lemma poissonKernel_nonneg_on_circle_local {z : ℂ} {R θ : ℝ} (hz : z ∈ ball (0 : ℂ) R) :
    0 ≤ poissonKernel 0 z (circleMap 0 R θ) := by
  have hR : 0 < R := pos_of_mem_ball hz
  have hz_norm_lt : ‖z‖ < R := by
    simpa [mem_ball, dist_eq_norm] using hz
  have hsphere : circleMap 0 R θ ∈ sphere (0 : ℂ) R := by
    simpa [abs_of_pos hR] using circleMap_mem_sphere (0 : ℂ) hR.le θ
  have hleft_nonneg : 0 ≤ (R - ‖z‖) / (R + ‖z‖) := by
    refine div_nonneg ?_ ?_
    · exact sub_nonneg.mpr hz_norm_lt.le
    · positivity
  -- Use the Herglotz lower bound and rewrite its real part back to the Poisson kernel.
  exact le_trans hleft_nonneg <| by
    simpa [poissonKernel_eq_re_herglotzRieszKernel, herglotzRieszKernel_def] using
      (le_re_herglotzRieszKernel (c := 0) (z := circleMap 0 R θ) (w := z) hsphere hz)

/-- Helper for Theorem IV.4-extra-2: the normalized near-arc translated Poisson error is bounded
by the boundary oscillation on that arc. -/
lemma translated_near_arc_error_le
    {φ : ℂ → ℝ} {c z : ℂ} {R θ₀ η ε : ℝ} (hz : z ∈ ball c R) (hε : 0 ≤ ε)
    (hosc :
      ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
        |((θ - θ₀ : Real.Angle)).toReal| ≤ η →
          |φ (circleMap c R θ) - φ (circleMap c R θ₀)| ≤ ε) :
    |(2 * Real.pi)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          indicator {θ : ℝ | |((θ - θ₀ : Real.Angle)).toReal| ≤ η}
            (fun θ : ℝ ↦
              poissonKernel 0 (z - c) (circleMap 0 R θ) *
                (φ (circleMap c R θ) - φ (circleMap c R θ₀))) θ ∂MeasureTheory.volume|
      ≤ ε := by
  have hz0 : z - c ∈ ball (0 : ℂ) R := by
    simpa [mem_ball, dist_eq_norm] using hz
  have hR : 0 < R := pos_of_mem_ball hz0
  let K : ℝ → ℝ := fun θ ↦ poissonKernel 0 (z - c) (circleMap 0 R θ)
  let near : Set ℝ := {θ : ℝ | |((θ - θ₀ : Real.Angle)).toReal| ≤ η}
  let full : ℝ → ℝ := fun θ ↦
    K θ * (φ (circleMap c R θ) - φ (circleMap c R θ₀))
  have hkernel_cont :
      ContinuousOn K (Set.Icc 0 (2 * Real.pi)) := by
    refine (poissonKernel_continuousOn_sphere_of_mem_ball_local hz0).comp'
      (continuous_circleMap 0 R).continuousOn ?_
    intro θ hθ
    simpa [K, abs_of_pos hR] using circleMap_mem_sphere (0 : ℂ) hR.le θ
  have hbound :
      IntervalIntegrable (fun θ : ℝ ↦ ε * K θ) MeasureTheory.volume 0 (2 * Real.pi) := by
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le Real.two_pi_pos.le).2 ?_
    exact (continuousOn_const.mul hkernel_cont).integrableOn_Icc
  have hpoint :
      ∀ θ ∈ Set.Ioc 0 (2 * Real.pi), ‖indicator near full θ‖ ≤ ε * K θ := by
    intro θ hθ
    have hk_nonneg : 0 ≤ K θ := by
      exact poissonKernel_nonneg_on_circle_local (θ := θ) hz0
    by_cases hnear : θ ∈ near
    · have hoscθ : |φ (circleMap c R θ) - φ (circleMap c R θ₀)| ≤ ε := by
        exact hosc θ (Set.Ioc_subset_Icc_self hθ) hnear
      -- On the near arc, the oscillation hypothesis controls the boundary difference.
      calc
        ‖indicator near full θ‖ = K θ * |φ (circleMap c R θ) - φ (circleMap c R θ₀)| := by
          simp [near, full, hnear, K, Real.norm_eq_abs, abs_of_nonneg hk_nonneg]
        _ ≤ K θ * ε := by
          gcongr
        _ = ε * K θ := by ring
    · -- Outside the near arc, the indicator vanishes.
      have hnonneg : 0 ≤ ε * K θ := mul_nonneg hε hk_nonneg
      simp [near, full, hnear, hnonneg]
  have hnorm :
      ‖∫ θ in (0 : ℝ)..(2 * Real.pi), indicator near full θ ∂MeasureTheory.volume‖
        ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), ε * K θ ∂MeasureTheory.volume := by
    exact intervalIntegral.norm_integral_le_of_norm_le Real.two_pi_pos.le
      (Eventually.of_forall fun θ hθ ↦ hpoint θ hθ) hbound
  have hmass :
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), K θ ∂MeasureTheory.volume = 1 := by
    -- Normalize the integral by identifying it with the Poisson average
    -- of the constant function `1`.
    simpa [K, Real.circleAverage_def, smul_eq_mul] using poisson_circleAverage_const_one hz0
  -- Multiply the integral estimate by the positive normalization factor,
  -- then use total mass `1`.
  calc
    |(2 * Real.pi)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), indicator near full θ ∂MeasureTheory.volume|
      = (2 * Real.pi)⁻¹ *
          ‖∫ θ in (0 : ℝ)..(2 * Real.pi), indicator near full θ ∂MeasureTheory.volume‖ := by
            rw [← Real.norm_eq_abs, norm_mul, Real.norm_of_nonneg (by positivity)]
    _ ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), ε * K θ ∂MeasureTheory.volume := by
          gcongr
    _ = ε * ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), K θ ∂MeasureTheory.volume) := by
          rw [intervalIntegral.integral_const_mul]
          ring
    _ = ε := by
          rw [hmass]
          ring

/-- Helper for Theorem IV.4-extra-2: the normalized far-arc translated Poisson error is controlled
by the truncated Poisson kernel average times a uniform boundary bound. -/
lemma translated_far_arc_error_le_kernel_tail
    {φ : ℂ → ℝ} {c z : ℂ} {R θ₀ η M : ℝ} (hz : z ∈ ball c R) (hηπ : η < Real.pi)
    (hM0 : 0 ≤ M)
    (hM :
      ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
        |φ (circleMap c R θ) - φ (circleMap c R θ₀)| ≤ M) :
    |(2 * Real.pi)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          indicator {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
            (fun θ : ℝ ↦
              poissonKernel 0 (z - c) (circleMap 0 R θ) *
                (φ (circleMap c R θ) - φ (circleMap c R θ₀))) θ ∂MeasureTheory.volume|
      ≤
        M * ((2 * Real.pi)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            indicator {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
              (fun θ : ℝ ↦ poissonKernel 0 (z - c) (circleMap 0 R θ)) θ
              ∂MeasureTheory.volume) := by
  have hz0 : z - c ∈ ball (0 : ℂ) R := by
    simpa [mem_ball, dist_eq_norm] using hz
  have hR : 0 < R := pos_of_mem_ball hz0
  let K : ℝ → ℝ := fun θ ↦ poissonKernel 0 (z - c) (circleMap 0 R θ)
  let far : Set ℝ := {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
  let full : ℝ → ℝ := fun θ ↦
    K θ * (φ (circleMap c R θ) - φ (circleMap c R θ₀))
  have hkernel_cont :
      ContinuousOn K (Set.Icc 0 (2 * Real.pi)) := by
    refine (poissonKernel_continuousOn_sphere_of_mem_ball_local hz0).comp'
      (continuous_circleMap 0 R).continuousOn ?_
    intro θ hθ
    simpa [K, abs_of_pos hR] using circleMap_mem_sphere (0 : ℂ) hR.le θ
  have htail_int :
      IntervalIntegrable (indicator far K) MeasureTheory.volume 0 (2 * Real.pi) := by
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le Real.two_pi_pos.le).2 ?_
    exact hkernel_cont.integrableOn_Icc.indicator
      (measurableSet_translated_far_arc_local (θ₀ := θ₀) hηπ)
  have hbound :
      IntervalIntegrable (fun θ : ℝ ↦ M * indicator far K θ) MeasureTheory.volume 0
        (2 * Real.pi) := by
    simpa [mul_comm] using htail_int.const_mul M
  have hpoint :
      ∀ θ ∈ Set.Ioc 0 (2 * Real.pi), ‖indicator far full θ‖ ≤ M * indicator far K θ := by
    intro θ hθ
    have hk_nonneg : 0 ≤ K θ := by
      exact poissonKernel_nonneg_on_circle_local (θ := θ) hz0
    by_cases hfar : θ ∈ far
    · have hMθ : |φ (circleMap c R θ) - φ (circleMap c R θ₀)| ≤ M := by
        exact hM θ (Set.Ioc_subset_Icc_self hθ)
      -- On the far arc, use the uniform boundary bound and kernel nonnegativity.
      calc
        ‖indicator far full θ‖ = K θ * |φ (circleMap c R θ) - φ (circleMap c R θ₀)| := by
          simp [far, full, hfar, K, Real.norm_eq_abs, abs_of_nonneg hk_nonneg]
        _ ≤ K θ * M := by
          gcongr
        _ = M * indicator far K θ := by
          simp [far, hfar, K, mul_comm]
    · -- Outside the far arc, the indicator vanishes.
      have hnonneg : 0 ≤ M * indicator far K θ := by
        rw [show indicator far K θ = 0 by simp [far, hfar]]
        positivity
      simp [far, full, hfar]
  have hnorm :
      ‖∫ θ in (0 : ℝ)..(2 * Real.pi), indicator far full θ ∂MeasureTheory.volume‖
        ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), M * indicator far K θ ∂MeasureTheory.volume := by
    exact intervalIntegral.norm_integral_le_of_norm_le Real.two_pi_pos.le
      (Eventually.of_forall fun θ hθ ↦ hpoint θ hθ) hbound
  -- Normalize the estimate and factor the constant `M` out of the kernel tail integral.
  calc
    |(2 * Real.pi)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), indicator far full θ ∂MeasureTheory.volume|
      = (2 * Real.pi)⁻¹ *
          ‖∫ θ in (0 : ℝ)..(2 * Real.pi), indicator far full θ ∂MeasureTheory.volume‖ := by
            rw [← Real.norm_eq_abs, norm_mul, Real.norm_of_nonneg (by positivity)]
    _ ≤ (2 * Real.pi)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi), M * indicator far K θ ∂MeasureTheory.volume := by
          gcongr
    _ = M * ((2 * Real.pi)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi), indicator far K θ ∂MeasureTheory.volume) := by
          rw [intervalIntegral.integral_const_mul]
          ring

/-- Helper for Theorem IV.4-extra-2: after translating to the centered disc, the far-arc piece of
the Poisson error tends to zero as the interior point approaches the chosen boundary point. -/
lemma translated_far_arc_error_tendsto_zero
    {φ : ℂ → ℝ} {c : ℂ} {R θ₀ η : ℝ} (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R))
    (hη : 0 < η) (hηπ : η < Real.pi) :
    Tendsto
      (fun z : ℂ ↦
        (2 * Real.pi)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            indicator {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
              (fun θ : ℝ ↦
                poissonKernel 0 (z - c) (circleMap 0 R θ) *
                  (φ (circleMap c R θ) - φ (circleMap c R θ₀))) θ
              ∂MeasureTheory.volume)
      (nhdsWithin (circleMap c R θ₀) (ball c R))
      (nhds 0) := by
  obtain ⟨M, hM0, hM⟩ :=
    boundary_difference_bounded_on_circle_interval (c := c) (R := R) (θ₀ := θ₀) hR hφ
  let boundary : ℂ := circleMap c R θ₀
  let tail : ℂ → ℝ := fun w ↦
    (2 * Real.pi)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        indicator {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
          (fun θ : ℝ ↦ poissonKernel 0 w (circleMap 0 R θ)) θ
          ∂MeasureTheory.volume
  have htail0 :
      Tendsto tail (nhdsWithin (circleMap (0 : ℂ) R θ₀) (ball (0 : ℂ) R)) (nhds 0) := by
    simpa [tail] using
      poisson_kernel_integral_away_from_boundary_angle_tendsto_zero_local
        (r := R) (θ₀ := θ₀) (η := η) hR hη
  have himage_ball : (fun z : ℂ ↦ z - c) '' ball c R = ball (0 : ℂ) R := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [mem_ball, dist_eq_norm] using hz
    · intro hw
      refine ⟨w + c, ?_, by simp⟩
      simpa [mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hw
  have htranslate :
      Tendsto (fun z : ℂ ↦ z - c)
        (nhdsWithin boundary (ball c R))
        (nhdsWithin (circleMap (0 : ℂ) R θ₀) (ball (0 : ℂ) R)) := by
    have hcont :
        ContinuousWithinAt (fun z : ℂ ↦ z - c) (ball c R) boundary :=
      (continuous_id.sub continuous_const).continuousWithinAt
    -- Translation sends the punctured approach region in `ball c R` to the centered one.
    simpa [boundary, himage_ball, circleMap, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hcont.tendsto_nhdsWithin_image
  have htail :
      Tendsto (fun z : ℂ ↦ tail (z - c))
        (nhdsWithin boundary (ball c R)) (nhds 0) := by
    exact htail0.comp htranslate
  have hbound :
      ∀ᶠ z in nhdsWithin boundary (ball c R),
        ‖(2 * Real.pi)⁻¹ *
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              indicator {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
                (fun θ : ℝ ↦
                  poissonKernel 0 (z - c) (circleMap 0 R θ) *
                    (φ (circleMap c R θ) - φ (circleMap c R θ₀))) θ
                ∂MeasureTheory.volume‖
          ≤ M * tail (z - c) := by
    -- Within the filter, points remain in the disc, so the far-arc domination lemma applies.
    filter_upwards [self_mem_nhdsWithin] with z hz
    simpa [tail, Real.norm_eq_abs] using
      translated_far_arc_error_le_kernel_tail
        (c := c) (z := z) (R := R) (θ₀ := θ₀) (η := η) (M := M) hz hηπ hM0 hM
  have htail_scaled : Tendsto (fun z : ℂ ↦ M * tail (z - c))
      (nhdsWithin boundary (ball c R)) (nhds 0) := by
    simpa using htail.const_mul M
  -- Squeeze the far-arc error by the truncated kernel tail, which already tends to zero.
  exact squeeze_zero_norm' hbound htail_scaled

/-- Helper for Theorem IV.4-extra-2: the Poisson average tends to the boundary value at every
boundary point of the disc. -/
lemma poisson_circleAverage_tendsto_boundary_at_circleMap
    {φ : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R)) (θ₀ : ℝ) :
    Tendsto (fun z ↦ Real.circleAverage (poissonKernel c z • φ) c R)
      (nhdsWithin (circleMap c R θ₀) (ball c R))
      (nhds (φ (circleMap c R θ₀))) := by
  -- Route correction: the remaining source-faithful step is the Poisson approximate-identity
  -- argument after translating to the centered disc.
  let boundary : ℂ := circleMap c R θ₀
  let near : ℝ → Set ℝ := fun η ↦ {θ : ℝ | |((θ - θ₀ : Real.Angle)).toReal| ≤ η}
  let far : ℝ → Set ℝ := fun η ↦ {θ : ℝ | η < |((θ - θ₀ : Real.Angle)).toReal|}
  let nearError : ℝ → ℂ → ℝ := fun η z ↦
    (2 * Real.pi)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        indicator (near η)
          (fun θ : ℝ ↦
            poissonKernel 0 (z - c) (circleMap 0 R θ) *
              (φ (circleMap c R θ) - φ boundary)) θ
          ∂MeasureTheory.volume
  let farError : ℝ → ℂ → ℝ := fun η z ↦
    (2 * Real.pi)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        indicator (far η)
          (fun θ : ℝ ↦
            poissonKernel 0 (z - c) (circleMap 0 R θ) *
              (φ (circleMap c R θ) - φ boundary)) θ
          ∂MeasureTheory.volume
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨η, hη, hηπ, hosc⟩ :=
    boundary_value_oscillation_small_of_angle_gap (c := c) (R := R) (θ₀ := θ₀) hR hφ
      (ε := ε / 2) (by positivity)
  have hfar_zero :
      Tendsto (farError η) (nhdsWithin boundary (ball c R)) (nhds 0) := by
    -- The far-arc contribution is exactly the kernel tail controlled in the previous helper.
    simpa [farError, far, boundary] using
      translated_far_arc_error_tendsto_zero (c := c) (R := R) (θ₀ := θ₀) (η := η) hR hφ hη hηπ
  rcases (Metric.tendsto_nhdsWithin_nhds.mp hfar_zero) (ε / 2) (by positivity) with
    ⟨δ, hδ, hfarδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro z hz hzd
  have htranslate :
      Real.circleAverage (poissonKernel c z • φ) c R - φ boundary =
        (2 * Real.pi)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            poissonKernel 0 (z - c) (circleMap 0 R θ) *
              (φ (circleMap c R θ) - φ boundary) ∂MeasureTheory.volume := by
    -- Rewrite the boundary error as the centered translated Poisson average.
    simpa [boundary, Real.circleAverage_def, smul_eq_mul, circleMap, add_assoc, add_left_comm,
      add_comm] using
      poisson_circleAverage_translate_sub_boundary_value (c := c) (z := z) (R := R) (θ₀ := θ₀)
        hφ hz
  have hnear_int :
      IntervalIntegrable
        (indicator (near η)
          (fun θ : ℝ ↦
            poissonKernel 0 (z - c) (circleMap 0 R θ) *
              (φ (circleMap c R θ) - φ boundary)))
        MeasureTheory.volume 0 (2 * Real.pi) := by
    -- The near cutoff preserves interval integrability on the compact angle interval.
    simpa [near, boundary] using
      translated_near_arc_intervalIntegrable_local
        (c := c) (z := z) (R := R) (θ₀ := θ₀) (η := η) hz hφ hηπ
  have hfar_int :
      IntervalIntegrable
        (indicator (far η)
          (fun θ : ℝ ↦
            poissonKernel 0 (z - c) (circleMap 0 R θ) *
              (φ (circleMap c R θ) - φ boundary)))
        MeasureTheory.volume 0 (2 * Real.pi) := by
    -- The same compactness argument handles the far cutoff.
    simpa [far, boundary] using
      translated_far_arc_intervalIntegrable_local
        (c := c) (z := z) (R := R) (θ₀ := θ₀) (η := η) hz hφ hηπ
  have hsplit :
      |(2 * Real.pi)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            poissonKernel 0 (z - c) (circleMap 0 R θ) * (φ (circleMap c R θ) - φ boundary)
              ∂MeasureTheory.volume|
        ≤ |nearError η z| + |farError η z| := by
    -- Split the full translated error into the near and far arcs.
    simpa [nearError, farError, near, far, boundary] using
      poisson_translated_error_split_near_far_interval
        (φ := φ) (c := c) (z := z) (R := R) (θ₀ := θ₀) (η := η) hnear_int hfar_int
  have hnear_le : |nearError η z| ≤ ε / 2 := by
    -- The near arc contributes at most the chosen boundary oscillation.
    simpa [nearError, near, boundary] using
      translated_near_arc_error_le
        (c := c) (z := z) (R := R) (θ₀ := θ₀) (η := η) (ε := ε / 2) hz
        (by positivity : 0 ≤ ε / 2)
        (fun θ hθ hnear ↦ by
          simpa [boundary] using hosc θ hnear)
  have hfar_lt : |farError η z| < ε / 2 := by
    simpa [Real.dist_eq] using hfarδ hz hzd
  -- Combine the near oscillation bound with the vanishing far tail.
  simpa [Real.dist_eq, boundary] using calc
    |Real.circleAverage (poissonKernel c z • φ) c R - φ boundary|
      = |(2 * Real.pi)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            poissonKernel 0 (z - c) (circleMap 0 R θ) *
              (φ (circleMap c R θ) - φ boundary) ∂MeasureTheory.volume| := by
            rw [htranslate]
    _ ≤ |nearError η z| + |farError η z| := hsplit
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hnear_le hfar_lt
    _ = ε := by ring

/-- Helper for Theorem IV.4-extra-2: once the interior Poisson branch has the correct boundary
limits, the piecewise boundary extension is continuous on the closed disc. -/
lemma poisson_boundary_extension_continuousOn_closedBall
    {φ : ℂ → ℝ} {c : ℂ} {R : ℝ} [DecidablePred fun z : ℂ => z ∈ ball c R]
    (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R))
    (hboundary :
      ∀ θ₀ : ℝ,
        Tendsto (fun z ↦ Real.circleAverage (poissonKernel c z • φ) c R)
          (nhdsWithin (circleMap c R θ₀) (ball c R))
          (nhds (φ (circleMap c R θ₀)))) :
    ContinuousOn
      (fun z ↦ if z ∈ ball c R then Real.circleAverage (poissonKernel c z • φ) c R else φ z)
      (closedBall c R) := by
  let u0 : ℂ → ℝ := fun z ↦ Real.circleAverage (poissonKernel c z • φ) c R
  have hu0_harm : HarmonicOnNhd u0 (ball c R) := poisson_circleAverage_harmonicOnNhd hR hφ
  have hu0_cont : ContinuousOn u0 (closedBall c R ∩ ball c R) := by
    -- The interior Poisson branch is harmonic, hence continuous, on the open disc.
    exact hu0_harm.continuousOn.mono fun z hz ↦ hz.2
  have hball :
      closedBall c R ∩ ball c R = ball c R := by
    ext z
    rw [mem_inter_iff, mem_closedBall, mem_ball]
    constructor
    · intro hz
      exact hz.2
    · intro hz
      exact ⟨le_of_lt hz, hz⟩
  have hsphere :
      closedBall c R ∩ (ball c R)ᶜ = sphere c R := by
    ext z
    rw [mem_inter_iff, mem_closedBall, mem_compl_iff, mem_ball, mem_sphere]
    constructor
    · intro hz
      exact le_antisymm hz.1 (not_lt.mp hz.2)
    · intro hz
      exact ⟨hz.le, by simpa [hz]⟩
  have hφ_cont : ContinuousOn φ (closedBall c R ∩ (ball c R)ᶜ) := by
    -- On the complementary closed-ball piece, we are exactly on the boundary sphere.
    simpa [hsphere] using hφ
  -- Paste the interior Poisson branch with the boundary datum across the frontier sphere.
  change ContinuousOn ((ball c R).piecewise u0 φ) (closedBall c R)
  refine ContinuousOn.piecewise' ?_ ?_ hu0_cont hφ_cont
  · intro z hz
    have hz_sphere : z ∈ sphere c R := by
      simpa [frontier_ball c hR.ne'] using hz.2
    have hz_image : z ∈ circleMap c R '' Set.Ioc 0 (2 * Real.pi) := by
      have : z ∈ sphere c |R| := by simpa [abs_of_pos hR] using hz_sphere
      rw [← image_circleMap_Ioc c R] at this
      exact this
    rcases hz_image with ⟨θ₀, hθ₀, rfl⟩
    have hcircle_sphere : circleMap c R θ₀ ∈ sphere c R := by
      simpa [abs_of_pos hR] using circleMap_mem_sphere c hR.le θ₀
    have hcircle_not_ball : circleMap c R θ₀ ∉ ball c R := by
      rw [mem_ball]
      rw [mem_sphere] at hcircle_sphere
      simpa [hcircle_sphere]
    -- The interior-side boundary condition is supplied by the boundary-limit theorem.
    simpa [u0, piecewise, hball, hcircle_not_ball] using hboundary θ₀
  · intro z hz
    have hz_sphere : z ∈ sphere c R := by
      simpa [frontier_ball c hR.ne'] using hz.2
    have hz_not_ball : z ∉ ball c R := by
      rw [mem_ball]
      rw [mem_sphere] at hz_sphere
      simpa [hz_sphere]
    -- On the boundary side, continuity of `φ` on the sphere gives the required limit.
    simpa [hsphere, piecewise, hz_not_ball] using hφ z hz_sphere

/-- Theorem IV.4-extra-2 (1). For continuous boundary data on the boundary circle of a disc, there
exists a real-valued function that is harmonic on the open disc, continuous on its closure, and
attains the prescribed boundary values.
-/
theorem dirichlet_problem_disc_exists {φ : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hφ : ContinuousOn φ (sphere c R)) :
    ∃ u : ℂ → ℝ, HarmonicContOnCl u (ball c R) ∧ EqOn u φ (sphere c R) := by
  rcases lt_trichotomy R 0 with hR | rfl | hR
  · refine ⟨fun _ ↦ 0, harmonicContOnCl_const, ?_⟩
    intro z hz
    rw [mem_sphere] at hz
    exfalso
    have hR' : 0 ≤ R := by simpa [hz] using (dist_nonneg : 0 ≤ dist z c)
    exact (not_lt_of_ge hR') hR
  · refine ⟨fun _ ↦ φ c, harmonicContOnCl_const, ?_⟩
    intro z hz
    rw [mem_sphere] at hz
    have hz' : z = c := dist_eq_zero.mp hz
    simp [hz']
  · -- Route correction: the intended proof still goes through the Poisson integral. The boundary
    -- regularity inputs now give the interior harmonicity of the Poisson extension. The remaining
    -- blocker is the boundary-limit argument needed to package the piecewise extension as
    -- `ContinuousOn` on `closedBall c R`.
    classical
    let u0 : ℂ → ℝ := fun z ↦ Real.circleAverage (poissonKernel c z • φ) c R
    let u : ℂ → ℝ := fun z ↦ if z ∈ ball c R then u0 z else φ z
    have hu0_harm : HarmonicOnNhd u0 (ball c R) := poisson_circleAverage_harmonicOnNhd hR hφ
    have hu_harm : HarmonicOnNhd u (ball c R) := by
      intro z hz
      have hEq : u =ᶠ[𝓝 z] u0 := by
        -- Inside the open disc the piecewise extension agrees with the Poisson integral locally.
        filter_upwards [isOpen_ball.mem_nhds hz] with y hy
        classical
        by_cases hyball : y ∈ ball c R
        · change (if y ∈ ball c R then u0 y else φ y) = u0 y
          simp [hyball]
        · exact False.elim (hyball hy)
      exact (harmonicAt_congr_nhds hEq).2 (hu0_harm z hz)
    have hu_boundary : EqOn u φ (sphere c R) := by
      intro z hz
      have hz_not_ball : z ∉ ball c R := by
        rw [mem_ball, mem_sphere] at *
        exact hz.not_lt
      change (if z ∈ ball c R then u0 z else φ z) = φ z
      simp [hz_not_ball]
    have hu_cont : ContinuousOn u (closedBall c R) := by
      have hboundary :
          ∀ θ₀ : ℝ,
            Tendsto (fun z ↦ u0 z)
              (nhdsWithin (circleMap c R θ₀) (ball c R))
              (nhds (φ (circleMap c R θ₀))) := by
        intro θ₀
        -- The only remaining analytic input is the boundary limit of the Poisson branch.
        simpa [u0] using
          poisson_circleAverage_tendsto_boundary_at_circleMap (c := c) (R := R) hR hφ θ₀
      -- Once the boundary limit is known, continuity on the closed ball is just a pasting step.
      simpa [u, u0] using
        poisson_boundary_extension_continuousOn_closedBall (c := c) (R := R) hR hφ hboundary
    exact ⟨u, HarmonicContOnCl.mk_ball hu_harm hu_cont, hu_boundary⟩

/-- Theorem IV.4-extra-2 (2). Two real-valued harmonic solutions of the Dirichlet problem on a disc
that agree on the boundary circle agree on the whole closed disc.
-/
theorem dirichlet_problem_disc_unique {u v : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hu : HarmonicContOnCl u (ball c R)) (hv : HarmonicContOnCl v (ball c R))
    (huv : EqOn u v (sphere c R)) :
    EqOn u v (closedBall c R) := by
  have hzero : EqOn (u - v) 0 (closedBall c R) :=
    (hu.sub hv).eqOn_zero_closedBall_of_eqOn_zero_sphere fun z hz ↦ sub_eq_zero.2 (huv hz)
  intro z hz
  exact sub_eq_zero.1 (hzero hz)
