import DifferentialForms_Cartan_1970.V.section18.«0004_Theorem_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set Metric
open scoped Topology

-- Semantic recall note: `lean_leansearch` was unavailable in this runner; local repo/API
-- inspection identified the chapter bridge
-- `differentiableOn_of_tendsto_locally_uniformly_on_compacts` together with the canonical owners
-- `analyticOnNhd_iff_differentiableOn`,
-- `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`,
-- `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`, and
-- `DiffContOnCl.ball_subset_image_closedBall`.

/-- Proposition 2.1: let `D` be a preconnected open subset of `ℂ`. If a sequence of holomorphic
functions on `D` converges uniformly on compact subsets of `D`, and if each term is nowhere zero
on `D`, then the limit is nowhere zero on `D` unless it is identically zero on `D`. -/
theorem nonvanishing_of_not_identically_zero_of_tendsto_locally_uniformly_on_compacts
    {D : Set ℂ} (hD_open : IsOpen D) (hD_preconnected : IsPreconnected D)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) D)
    (hconv : TendstoLocallyUniformlyOn F f atTop D)
    (hF_nonvanishing : ∀ n z, z ∈ D → F n z ≠ 0)
    (hf_not_identically_zero : ¬ EqOn f 0 D) :
    ∀ z ∈ D, f z ≠ 0 := by
  have hf_holo : DifferentiableOn ℂ f D :=
    differentiableOn_of_tendsto_locally_uniformly_on_compacts hD_open hF hconv
  have hf_analytic : AnalyticOnNhd ℂ f D :=
    (Complex.analyticOnNhd_iff_differentiableOn hD_open).2 hf_holo
  intro z hz
  by_contra hfz
  have hfz : f z = 0 := by simpa using hfz
  have hf_punctured_nonzero : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
    rcases (hf_analytic z hz).eventually_eq_zero_or_eventually_ne_zero with hf_zero | hf_nonzero
    · exact False.elim <| hf_not_identically_zero <|
        hf_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero hD_preconnected hz hf_zero
    · exact hf_nonzero
  rcases Metric.mem_nhds_iff.mp (hD_open.mem_nhds hz) with ⟨ρ, hρ_pos, hρD⟩
  rcases Metric.mem_nhdsWithin_iff.mp hf_punctured_nonzero with ⟨δ, hδ_pos, hδf⟩
  let r : ℝ := min (δ / 2) (ρ / 2)
  have hr_pos : 0 < r := by
    refine lt_min ?_ ?_
    · exact half_pos hδ_pos
    · exact half_pos hρ_pos
  have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ_pos)
  have hrρ : r < ρ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρ_pos)
  have hclosedD : closedBall z r ⊆ D := (closedBall_subset_ball hrρ).trans hρD
  have hsphere_nonzero : ∀ w ∈ sphere z r, f w ≠ 0 := by
    intro w hw
    exact hδf
      ⟨(closedBall_subset_ball hrδ) (sphere_subset_closedBall hw), ne_of_mem_sphere hw hr_pos.ne'⟩
  have hsphere_nonempty : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr_pos.le
  have hnorm_cont : ContinuousOn (fun w ↦ ‖f w‖) (sphere z r) :=
    continuous_norm.comp_continuousOn <|
      hf_holo.continuousOn.mono (sphere_subset_closedBall.trans hclosedD)
  obtain ⟨w₀, hw₀, hw₀_min⟩ := (isCompact_sphere z r).exists_isMinOn hsphere_nonempty hnorm_cont
  let ε : ℝ := ‖f w₀‖
  have hε_pos : 0 < ε := by
    simp [ε, hsphere_nonzero w₀ hw₀]
  have hε_le : ∀ w ∈ sphere z r, ε ≤ ‖f w‖ := by
    intro w hw
    simpa [ε] using hw₀_min hw
  have hconv_closed :
      TendstoUniformlyOn F f atTop (closedBall z r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD_open).mp hconv
      (closedBall z r) hclosedD (isCompact_closedBall z r)
  rw [uniformity_basis_dist.tendstoUniformlyOn_iff_of_uniformity] at hconv_closed
  have hclose : ∀ᶠ n in atTop, ∀ w ∈ closedBall z r, dist (f w) (F n w) < ε / 4 :=
    hconv_closed (ε / 4) (by positivity)
  rcases Filter.eventually_atTop.1 hclose with ⟨N, hN⟩
  have hFN_analytic : AnalyticOnNhd ℂ (F N) D :=
    (Complex.analyticOnNhd_iff_differentiableOn hD_open).2 (hF N)
  have hFN_diffCont : DiffContOnCl ℂ (F N) (ball z r) :=
    DiffContOnCl.mk_ball
      ((hF N).mono (ball_subset_closedBall.trans hclosedD))
      ((hF N).continuousOn.mono hclosedD)
  have hFN_center : ‖F N z‖ < ε / 4 := by
    simpa [dist_eq_norm, hfz, ε] using hN N le_rfl z (mem_closedBall_self hr_pos.le)
  have hFN_boundary : ∀ w ∈ sphere z r, ε / 2 ≤ ‖F N w - F N z‖ := by
    intro w hw
    have hFw_close : ‖f w - F N w‖ < ε / 4 := by
      simpa [dist_eq_norm] using hN N le_rfl w (sphere_subset_closedBall hw)
    have hFw_norm : 3 * ε / 4 < ‖F N w‖ := by
      have : ε < ‖F N w‖ + ε / 4 := by
        calc
          ε ≤ ‖f w‖ := hε_le w hw
          _ ≤ ‖F N w‖ + ‖f w - F N w‖ := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              norm_add_le (F N w) (f w - F N w)
          _ < ‖F N w‖ + ε / 4 := add_lt_add_right hFw_close _
      linarith
    have : ‖F N w‖ ≤ ‖F N w - F N z‖ + ‖F N z‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        norm_add_le (F N w - F N z) (F N z)
    linarith
  have hFN_not_eventually_eq : ¬ ∀ᶠ w in 𝓝 z, F N w = F N z := by
    intro hconst
    have hFN_const : EqOn (F N) (fun _ ↦ F N z) D :=
      hFN_analytic.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
        hD_preconnected hz hconst
    have : ¬ ε / 2 ≤ ‖F N w₀ - F N z‖ := by
      rw [hFN_const (hclosedD (sphere_subset_closedBall hw₀))]
      simp [hε_pos]
    exact this (hFN_boundary w₀ hw₀)
  have hFN_frequently_ne : ∃ᶠ w in 𝓝 z, F N w ≠ F N z :=
    not_eventually.mp hFN_not_eventually_eq
  have hzero_mem : (0 : ℂ) ∈ ball (F N z) (ε / 2 / 2) := by
    have hquarter : ε / 2 / 2 = ε / 4 := by ring
    simpa [dist_eq_norm, hquarter] using hFN_center
  rcases
      hFN_diffCont.ball_subset_image_closedBall hr_pos hFN_boundary hFN_frequently_ne hzero_mem with
    ⟨w, hw_ball, hw_zero⟩
  exact (hF_nonvanishing N w (hclosedD hw_ball)) hw_zero
