import DifferentialForms_Cartan_1970.cartan.III.section08.«0001_Definition_III_2_extra_1»

open Complex Metric Real Set
open scoped Topology

/-- Helper for Theorem 1: shrink a local maximum on an open set to a closed ball on which the same
pointwise upper bound holds. -/
lemma exists_pos_closedBall_subset_of_isLocalMaxOn
    {u : ℂ → ℝ} {D : Set ℂ} {a : ℂ}
    (hD : IsOpen D) (ha : a ∈ D) (hmax : IsLocalMaxOn u D a) :
    ∃ R > 0, closedBall a R ⊆ D ∧ ∀ z ∈ closedBall a R, u z ≤ u a := by
  -- Combine openness of `D` with the local-max filter condition to get one ordinary neighborhood.
  have hneigh : {z | z ∈ D ∧ u z ≤ u a} ∈ 𝓝 a := by
    have hD_neigh : D ∈ 𝓝 a := hD.mem_nhds ha
    have hmax_neigh : ∀ᶠ z in 𝓝 a, z ∈ D → u z ≤ u a :=
      (eventually_nhdsWithin_iff.1 <| by simpa [IsLocalMaxOn, IsMaxFilter] using hmax)
    filter_upwards [hD_neigh, hmax_neigh] with z hzD hzmax
    exact ⟨hzD, hzmax hzD⟩
  obtain ⟨R, hR_pos, hR_sub⟩ := Metric.mem_nhds_iff.mp hneigh
  refine ⟨R / 2, half_pos hR_pos, ?_, ?_⟩
  · -- The smaller closed ball sits inside the neighborhood ball and hence inside `D`.
    intro z hz
    exact (hR_sub <| closedBall_subset_ball (half_lt_self hR_pos) hz).1
  · -- On the same smaller closed ball, the local-max bound is valid pointwise.
    intro z hz
    exact (hR_sub <| closedBall_subset_ball (half_lt_self hR_pos) hz).2

/-- Helper for Theorem 1: multiplication by a constant preserves the mean value property. -/
lemma HasMeanValuePropertyOn.const_mul
    {f : ℂ → ℂ} {D : Set ℂ} (hf : HasMeanValuePropertyOn f D) (c : ℂ) :
    HasMeanValuePropertyOn (fun z ↦ c * f z) D := by
  -- This is the canonical real-linear map route, so the circle-average identity transports cleanly.
  simpa using hf.comp_CLM (ContinuousLinearMap.mul ℝ ℂ c)

/-- Helper for Theorem 1: if a continuous real-valued function on a circle is everywhere at most
`M` and somewhere strictly below `M`, then its circle average is strictly below `M`. -/
lemma circleAverage_lt_of_exists_lt_on_sphere
    {u : ℂ → ℝ} {a : ℂ} {r M : ℝ}
    (hr : 0 < r) (hcont : ContinuousOn u (sphere a r))
    (hle : ∀ z ∈ sphere a r, u z ≤ M) (hlt : ∃ z ∈ sphere a r, u z < M) :
    circleAverage u a r < M := by
  -- Parametrize the circle by `circleMap`; strict inequality at one point forces strict inequality
  -- of the interval integrals, and hence of the circle averages.
  rw [← circleAverage_const M a r]
  obtain ⟨z, hz, hzlt⟩ := hlt
  have hz_abs : z ∈ sphere a |r| := by simpa [abs_of_pos hr] using hz
  rw [← image_circleMap_Ioc a r] at hz_abs
  obtain ⟨θ₀, hθ₀, rfl⟩ := hz_abs
  have hcont_theta : Continuous (fun θ : ℝ ↦ u (circleMap a r θ)) := by
    exact hcont.comp_continuous (continuous_circleMap a r) (circleMap_mem_sphere a hr.le)
  have hlt_int :
      ∫ θ in 0..2 * π, u (circleMap a r θ) < ∫ θ in 0..2 * π, M := by
    refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      Real.two_pi_pos hcont_theta.continuousOn continuousOn_const ?_ ?_
    · intro θ hθ
      exact hle _ (circleMap_mem_sphere a hr.le θ)
    · exact ⟨θ₀, Set.Ioc_subset_Icc_self hθ₀, by simpa using hzlt⟩
  have hlt_avg :
      (2 * π)⁻¹ * (∫ θ in 0..2 * π, u (circleMap a r θ)) <
        (2 * π)⁻¹ * (∫ θ in 0..2 * π, M) :=
    mul_lt_mul_of_pos_left hlt_int (inv_pos.2 Real.two_pi_pos)
  simpa [circleAverage, smul_eq_mul] using hlt_avg

/-- Helper for Theorem 1: a continuous real-valued function on a circle whose average already
equals its pointwise upper bound must be constant on that circle. -/
lemma eqOn_sphere_of_circleAverage_eq_of_le
    {u : ℂ → ℝ} {a : ℂ} {r M : ℝ}
    (hr : 0 < r) (hcont : ContinuousOn u (sphere a r))
    (hle : ∀ z ∈ sphere a r, u z ≤ M) (havg : circleAverage u a r = M) :
    EqOn u (Function.const ℂ M) (sphere a r) := by
  intro z hz
  by_contra hz_ne
  -- Any strict drop below `M` would force a strict drop of the average, contradicting `havg`.
  have hz_lt : u z < M := lt_of_le_of_ne (hle z hz) hz_ne
  have hlt_avg : circleAverage u a r < M :=
    circleAverage_lt_of_exists_lt_on_sphere hr hcont hle ⟨z, hz, hz_lt⟩
  have : ¬ circleAverage u a r < M := by rw [havg]; exact lt_irrefl M
  exact this hlt_avg

/-- Helper for Theorem 1: a real-valued function with the mean value property and a local maximum
is locally constant. -/
lemma eventuallyEq_const_of_real_hasMeanValuePropertyOn_of_local_max
    {u : ℂ → ℝ} {D : Set ℂ} {a : ℂ}
    (hD : IsOpen D) (hu : HasMeanValuePropertyOn u D)
    (ha : a ∈ D) (hmax : IsLocalMaxOn u D a) :
    u =ᶠ[𝓝[D] a] Function.const ℂ (u a) := by
  obtain ⟨R, hR_pos, hclosedD, hle_closed⟩ :=
    exists_pos_closedBall_subset_of_isLocalMaxOn hD ha hmax
  rw [eventuallyEq_nhdsWithin_iff]
  refine Metric.eventually_nhds_iff.2 ?_
  refine ⟨R, hR_pos, fun z hzball _hzD ↦ ?_⟩
  let r : ℝ := dist z a
  by_cases hr0 : r = 0
  · -- Radius zero means that the point is the center itself.
    have hza : z = a := by simpa [r] using hr0
    simp [Function.const, hza]
  · -- For positive radius `r = dist z a`, the mean value property forces constancy on the sphere.
    have hr : 0 < r := by
      have hr_nonneg : 0 ≤ r := by simp [r]
      exact lt_of_le_of_ne hr_nonneg (Ne.symm hr0)
    have hz_closed : z ∈ closedBall a R := ball_subset_closedBall hzball
    have hr_le_R : r ≤ R := by simpa [r] using hz_closed
    have hclosed_rD : closedBall a r ⊆ D := by
      intro w hw
      apply hclosedD
      exact le_trans hw hr_le_R
    have hclosed_rR : closedBall a r ⊆ closedBall a R := by
      intro w hw
      exact le_trans hw hr_le_R
    have hsphere_cont : ContinuousOn u (sphere a r) := by
      exact hu.continuousOn.mono (sphere_subset_closedBall.trans hclosed_rD)
    have hsphere_le : ∀ w ∈ sphere a r, u w ≤ u a := by
      intro w hw
      exact hle_closed w (hclosed_rR <| sphere_subset_closedBall hw)
    have havg : circleAverage u a r = u a := by
      have hclosed_abs : closedBall a |r| ⊆ D := by
        simpa [abs_of_nonneg hr.le] using hclosed_rD
      simpa [abs_of_nonneg hr.le] using hu.circleAverage_eq (R := r) hclosed_abs
    have hsphere_eq :
        EqOn u (Function.const ℂ (u a)) (sphere a r) :=
      eqOn_sphere_of_circleAverage_eq_of_le hr hsphere_cont hsphere_le havg
    have hz_sphere : z ∈ sphere a r := by
      simp [r, dist_eq_norm]
    simpa using hsphere_eq hz_sphere

/-- Helper for Theorem 1: if a complex number has real part `M` and norm at most `M`, then it is
equal to the real number `M`. -/
lemma eq_of_re_eq_of_norm_le
    {w : ℂ} {M : ℝ} (hre : w.re = M) (hnorm : ‖w‖ ≤ M) :
    w = M := by
  -- Equality in `re z ≤ ‖z‖` forces the imaginary part to vanish and the real part to be `M`.
  have hw : w = ‖w‖ := (RCLike.norm_le_re_iff_eq_norm (z := w)).1 <| by simpa [hre] using hnorm
  have hnorm_eq : ‖w‖ = M := by
    calc
      ‖w‖ = w.re := by simpa using congrArg Complex.re hw |>.symm
      _ = M := hre
  simpa [hnorm_eq] using hw

/-- Theorem 1: if a complex-valued function on an open set has the mean value property
and its modulus has a relative maximum at `a`, then `f` is locally constant at `a` within `D`;
equivalently, it is constant on some open neighborhood of `a` contained in the domain. -/
theorem maximum_modulus_principle
    {f : ℂ → ℂ} {D : Set ℂ} {a : ℂ}
    (hD : IsOpen D) (hf_mean : HasMeanValuePropertyOn f D)
    (ha : a ∈ D) (hmax : IsLocalMaxOn (norm ∘ f) D a) :
    f =ᶠ[𝓝[D] a] Function.const ℂ (f a) := by
  obtain ⟨R, hR_pos, hclosedD, hnorm_closed⟩ :=
    exists_pos_closedBall_subset_of_isLocalMaxOn hD ha hmax
  by_cases hfa0 : f a = 0
  · -- If the center value is zero, the local norm bound already forces local vanishing.
    rw [eventuallyEq_nhdsWithin_iff]
    refine Metric.eventually_nhds_iff.2 ?_
    refine ⟨R, hR_pos, fun z hzball _hzD ↦ ?_⟩
    have hz_closed : z ∈ closedBall a R := ball_subset_closedBall hzball
    have hnorm_z : ‖f z‖ ≤ 0 := by
      simpa [Function.comp_apply, hfa0] using hnorm_closed z hz_closed
    have hnorm_zero : ‖f z‖ = 0 := le_antisymm hnorm_z (norm_nonneg _)
    simpa [hfa0] using norm_eq_zero.mp hnorm_zero
  · -- Route correction: rotate `f` so that the center value becomes the positive real `‖f a‖`,
    -- apply the real-valued maximum principle to the real part, then close using the norm bound.
    let c : ℂ := ‖f a‖ / f a
    have hfa_norm_ne : ‖f a‖ ≠ 0 := norm_ne_zero_iff.mpr hfa0
    have hc_norm : ‖c‖ = 1 := by
      dsimp [c]
      rw [norm_div]
      have hnorm_ofReal : ‖((‖f a‖ : ℝ) : ℂ)‖ = ‖f a‖ := by simp
      rw [hnorm_ofReal, div_self hfa_norm_ne]
    have hc_mul_center : c * f a = ‖f a‖ := by
      dsimp [c]
      field_simp [hfa0]
    have hc_ne : c ≠ 0 := by
      dsimp [c]
      refine div_ne_zero ?_ ?_
      · exact_mod_cast hfa_norm_ne
      · simpa using hfa0
    have hreal_mean : HasMeanValuePropertyOn (fun z ↦ (c * f z).re) D :=
      (hf_mean.const_mul c).real_part
    have hreal_max : IsLocalMaxOn (fun z ↦ (c * f z).re) D a := by
      -- The rotated real part stays below the norm, while it matches the norm at the center.
      rw [IsLocalMaxOn, IsMaxFilter, eventually_nhdsWithin_iff]
      refine Metric.eventually_nhds_iff.2 ?_
      refine ⟨R, hR_pos, fun z hzball _hzD ↦ ?_⟩
      have hz_closed : z ∈ closedBall a R := ball_subset_closedBall hzball
      calc
        (c * f z).re ≤ ‖c * f z‖ := Complex.re_le_norm _
        _ = ‖c‖ * ‖f z‖ := by rw [norm_mul]
        _ = ‖f z‖ := by rw [hc_norm, one_mul]
        _ ≤ ‖f a‖ := hnorm_closed z hz_closed
        _ = (c * f a).re := by simp [hc_mul_center]
    have hreal_eq :
        (fun z ↦ (c * f z).re) =ᶠ[𝓝[D] a] Function.const ℂ ‖f a‖ := by
      simpa [hc_mul_center] using
        eventuallyEq_const_of_real_hasMeanValuePropertyOn_of_local_max hD hreal_mean ha hreal_max
    have hnorm_event : ∀ᶠ z in 𝓝[D] a, ‖f z‖ ≤ ‖f a‖ := by
      simpa [IsLocalMaxOn, IsMaxFilter, Function.comp_apply] using hmax
    filter_upwards [hreal_eq, hnorm_event] with z hz_re hz_norm
    have hrot_norm : ‖c * f z‖ ≤ ‖f a‖ := by
      simpa [norm_mul, hc_norm] using hz_norm
    have hrot_eq : c * f z = c * f a := by
      calc
        c * f z = ‖f a‖ := eq_of_re_eq_of_norm_le hz_re hrot_norm
        _ = c * f a := hc_mul_center.symm
    exact mul_left_cancel₀ hc_ne hrot_eq
