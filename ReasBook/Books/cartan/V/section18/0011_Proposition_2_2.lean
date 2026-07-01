import cartan.V.section18.«0009_Proposition_2_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Metric Set
open scoped Topology

-- Domain sampling: this proposition is source-facing in the complex locally-uniform convergence /
-- holomorphic-injectivity domain. The core owners used here are `Set.InjOn` for simplicity on a
-- set, `TendstoLocallyUniformlyOn` for compacta convergence, and the earlier chapter theorem
-- `nonvanishing_of_not_identically_zero_of_tendsto_locally_uniformly_on_compacts`, which is the
-- canonical bridge from local uniform convergence to a nonvanishing limit statement.

/-- Proposition 2.2: let `D` be a preconnected open subset of `ℂ`. If a sequence of holomorphic
functions on `D` converges uniformly on compact subsets of `D`, and if each term is simple on `D`,
then the limit function is simple on `D` provided it is not constant on `D`. -/
theorem injOn_of_tendsto_locally_uniformly_on_compacts_of_not_eqOn_const
    {D : Set ℂ} (hD_open : IsOpen D) (hD_preconnected : IsPreconnected D)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF_holo : ∀ n, DifferentiableOn ℂ (F n) D)
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop D)
    (hF_simple : ∀ n, Set.InjOn (F n) D)
    (hf_not_const : ¬ ∃ c : ℂ, Set.EqOn f (fun _ ↦ c) D) :
    Set.InjOn f D := by
  have hf_holo : DifferentiableOn ℂ f D :=
    differentiableOn_of_tendsto_locally_uniformly_on_compacts hD_open hF_holo hconv
  intro x hx y hy hxy
  by_contra hxy_ne
  have hdist_pos : 0 < dist x y := dist_pos.mpr hxy_ne
  rcases Metric.mem_nhds_iff.mp (hD_open.mem_nhds hx) with ⟨ρ, hρ_pos, hρD⟩
  let r : ℝ := min (ρ / 2) (dist x y / 2)
  have hr_pos : 0 < r := by
    refine lt_min (half_pos hρ_pos) (half_pos hdist_pos)
  have hrρ : r < ρ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ_pos)
  have hrdist : r < dist x y := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hdist_pos)
  have hballD : ball x r ⊆ D := (ball_subset_ball hrρ.le).trans hρD
  have hy_not_mem_ball : y ∉ ball x r := by
    intro hy_ball
    exact (lt_irrefl (dist x y)) <| by simpa [dist_comm] using lt_of_lt_of_le hy_ball hrdist.le
  let G : ℕ → ℂ → ℂ := fun n z ↦ F n z - F n y
  let g : ℂ → ℂ := fun z ↦ f z - f y
  have hg_analytic : AnalyticOnNhd ℂ g D := by
    refine (Complex.analyticOnNhd_iff_differentiableOn hD_open).2 ?_
    simpa [g] using hf_holo.sub_const (f y)
  have hG_holo : ∀ n, DifferentiableOn ℂ (G n) (ball x r) := by
    intro n
    simpa [G] using ((hF_holo n).mono hballD).sub_const (F n y)
  have hconv_y :
      TendstoLocallyUniformlyOn (fun n _ ↦ F n y) (fun _ ↦ f y) atTop (ball x r) :=
    hconv.comp (fun _ ↦ y) (fun _ _ ↦ hy) continuousOn_const
  have hconv_G : TendstoLocallyUniformlyOn G g atTop (ball x r) := by
    let hsub : UniformContinuous (fun p : ℂ × ℂ ↦ p.1 - p.2) :=
      uniformContinuous_fst.sub uniformContinuous_snd
    exact hsub.comp_tendstoLocallyUniformlyOn ((hconv.mono hballD).prodMk hconv_y)
  have hG_nonvanishing : ∀ n z, z ∈ ball x r → G n z ≠ 0 := by
    intro n z hz hGz
    have hzy : z = y := hF_simple n (hballD hz) hy <| sub_eq_zero.mp <| by simpa [G] using hGz
    exact hy_not_mem_ball (hzy ▸ hz)
  have hg_not_identically_zero : ¬ EqOn g 0 (ball x r) := by
    intro hg_zero
    have hzero_nhds : ∀ᶠ z in 𝓝 x, g z = 0 := by
      refine mem_of_superset (ball_mem_nhds x hr_pos) ?_
      intro z hz
      exact hg_zero hz
    have hg_zero_D : EqOn g 0 D :=
      hg_analytic.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hD_preconnected hx
        hzero_nhds
    exact hf_not_const ⟨f y, fun z hz ↦ by simpa [g, sub_eq_zero] using hg_zero_D hz⟩
  have hg_nonvanishing :
      ∀ z ∈ ball x r, g z ≠ 0 :=
    nonvanishing_of_not_identically_zero_of_tendsto_locally_uniformly_on_compacts isOpen_ball
      (convex_ball x r).isPreconnected hG_holo hconv_G hG_nonvanishing hg_not_identically_zero
  exact hg_nonvanishing x (mem_ball_self hr_pos) <| by simp [g, hxy]
