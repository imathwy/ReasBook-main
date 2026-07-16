import Mathlib
import DifferentialForms_Cartan_1970.cartan.III.section10.«0008_Definition_III_4_extra_6»

-- Declarations for this item will be appended below by the statement pipeline.

open Set Metric Topology Filter

open scoped Topology

/-- Helper for Theorem III.4-extra-7: if the image of a set in `ℂ` is not dense, then some open
ball is disjoint from that image. -/
lemma exists_ball_disjoint_of_not_dense_image {s : Set ℂ} {f : ℂ → ℂ}
    (hnot_dense : ¬ Dense (f '' s)) :
    ∃ a r, 0 < r ∧ Disjoint (Metric.ball a r) (f '' s) := by
  -- Translate the negation of density into an explicitly missing metric ball.
  rw [Metric.dense_iff] at hnot_dense
  push Not at hnot_dense
  rcases hnot_dense with ⟨a, r, hr, hempty⟩
  exact ⟨a, r, hr, Set.disjoint_iff_inter_eq_empty.mpr hempty⟩

/-- Helper for Theorem III.4-extra-7: a ball missing the image forces `f - a` to be nonzero on the
source set. -/
lemma sub_const_ne_zero_of_ball_disjoint {s : Set ℂ} {f : ℂ → ℂ} {a : ℂ} {r : ℝ}
    (hr : 0 < r) (hdisj : Disjoint (Metric.ball a r) (f '' s)) :
    ∀ z ∈ s, f z - a ≠ 0 := by
  -- A zero of `f z - a` would map `z` to the center `a`, which lies in the missing ball.
  intro z hz hzero
  have hzball : f z ∈ Metric.ball a r := by
    have hfa : f z = a := sub_eq_zero.mp hzero
    rw [hfa, Metric.mem_ball]
    simpa using hr
  have hzimage : f z ∈ f '' s := ⟨z, hz, rfl⟩
  exact Set.disjoint_left.mp hdisj hzball hzimage

/-- Helper for Theorem III.4-extra-7: if the image misses a ball of radius `r`, then the reciprocal
`(f - a)⁻¹` is bounded by `r⁻¹` on the source set. -/
lemma norm_inv_sub_le_inv_radius_of_ball_disjoint {s : Set ℂ} {f : ℂ → ℂ} {a : ℂ} {r : ℝ}
    (hr : 0 < r) (hdisj : Disjoint (Metric.ball a r) (f '' s)) :
    ∀ z ∈ s, ‖(f z - a)⁻¹‖ ≤ r⁻¹ := by
  -- Excluding the image ball gives the lower bound `r ≤ ‖f z - a‖`, hence the reciprocal bound.
  intro z hz
  have hnot_ball : f z ∉ Metric.ball a r := by
    intro hzball
    have hzimage : f z ∈ f '' s := ⟨z, hz, rfl⟩
    exact Set.disjoint_left.mp hdisj hzball hzimage
  have hnorm_ge : r ≤ ‖f z - a‖ := by
    rw [Metric.mem_ball, Complex.dist_eq] at hnot_ball
    exact le_of_not_gt hnot_ball
  rw [norm_inv]
  have hnorm_pos : 0 < ‖f z - a‖ := lt_of_lt_of_le hr hnorm_ge
  exact (inv_le_inv₀ hnorm_pos hr).2 hnorm_ge

/-- Theorem III.4-extra-7: if `f` is holomorphic on a punctured disc around `0` and `0` is an
isolated essential singularity, then the image of every smaller punctured disc is dense in `ℂ`. -/
-- Proof sketch: If some open ball centered at `a` misses the image of the smaller punctured disc,
-- then `z ↦ (f z - a)⁻¹` is holomorphic and bounded on that punctured disc. The removable
-- singularity theorem extends this reciprocal holomorphically across `0`, so `f` becomes
-- meromorphic at `0`, contradicting that the singularity is essential.
theorem weierstrass_dense_image_of_isolated_essential_singularity
    {f : ℂ → ℂ} {ε : ℝ}
    (hess : HasEssentialSingularityAt f 0) (hε : 0 < ε)
    (h_analytic : AnalyticOnNhd ℂ f (ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    Dense (f '' (ball (0 : ℂ) ε \ ({0} : Set ℂ))) := by
  let s : Set ℂ := ball (0 : ℂ) ε \ ({0} : Set ℂ)
  by_contra hnot_dense
  rcases exists_ball_disjoint_of_not_dense_image (s := s) (f := f) hnot_dense with
    ⟨a, r, hr, hdisj⟩
  let g : ℂ → ℂ := fun z ↦ (f z - a)⁻¹
  have hsub_ne : ∀ z ∈ s, f z - a ≠ 0 :=
    sub_const_ne_zero_of_ball_disjoint (s := s) (f := f) (a := a) hr hdisj
  have hg_analytic : AnalyticOnNhd ℂ g s := by
    -- The source proof's key object is the reciprocal of `f - a` on the punctured disc.
    have hsub_analytic : AnalyticOnNhd ℂ (fun z ↦ f z - a) s := by
      simpa [s] using h_analytic.sub analyticOnNhd_const
    simpa [g] using hsub_analytic.inv hsub_ne
  have hs_nhds : s ∈ 𝓝[≠] (0 : ℂ) := by
    -- The punctured disc itself is a neighborhood inside the punctured-neighborhood filter.
    rw [show s = ball (0 : ℂ) ε ∩ ({(0 : ℂ)}ᶜ) by
      ext z
      simp [s, Set.diff_eq]]
    exact Metric.mem_nhdsWithin_iff.mpr ⟨ε, hε, subset_rfl⟩
  have hg_bound : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖g z‖ ≤ r⁻¹ := by
    -- The missing image ball gives the eventual uniform bound on the reciprocal.
    refine Filter.mem_of_superset hs_nhds ?_
    intro z hz
    exact norm_inv_sub_le_inv_radius_of_ball_disjoint (s := s) (f := f) (a := a) hr hdisj z hz
  have hg_diff : ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ g z := by
    -- Analyticity on the punctured disc supplies the punctured differentiability hypothesis.
    refine Filter.mem_of_superset hs_nhds ?_
    intro z hz
    exact (hg_analytic z hz).differentiableAt
  have hg_bounded_sub :
      IsBoundedUnder (· ≤ ·) (𝓝[≠] (0 : ℂ)) (fun z ↦ ‖g z - g 0‖) := by
    -- A bound on `‖g z‖` yields the removable-singularity boundedness condition for `g z - g 0`.
    have h_event : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖g z - g 0‖ ≤ r⁻¹ + ‖g 0‖ := by
      filter_upwards [hg_bound] with z hz
      exact norm_sub_le_of_le hz le_rfl
    exact isBoundedUnder_of_eventually_le h_event
  have htendsto_g : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (limUnder (𝓝[≠] (0 : ℂ)) g)) :=
    Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
      hg_diff hg_bounded_sub
  let ĝ : ℂ → ℂ := Function.update g 0 (limUnder (𝓝[≠] (0 : ℂ)) g)
  have hĝ_diff : ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ ĝ z := by
    -- Updating only the center leaves the punctured differentiability unchanged.
    filter_upwards [hg_diff, self_mem_nhdsWithin] with z hz hz0
    have h_eq : ĝ =ᶠ[𝓝 z] g := by
      filter_upwards [show ∀ᶠ w in 𝓝 z, w ≠ 0 from IsOpen.mem_nhds isOpen_ne hz0] with w hw
      simp [ĝ, Function.update_of_ne hw]
    exact hz.congr_of_eventuallyEq h_eq
  have hĝ_cont : ContinuousAt ĝ 0 := continuousAt_update_same.2 htendsto_g
  have hĝ_analytic : AnalyticAt ℂ ĝ 0 :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hĝ_diff hĝ_cont
  have hg_eq : g =ᶠ[𝓝[≠] (0 : ℂ)] ĝ := by
    -- Away from the center, the updated function agrees with the original reciprocal.
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp [ĝ, Function.update_of_ne hz]
  have hg_meromorphic : MeromorphicAt g 0 := by
    -- The removable extension makes `g` meromorphic at the singular point.
    exact hĝ_analytic.meromorphicAt.congr hg_eq.symm
  have hg_inv_meromorphic : MeromorphicAt (fun z ↦ (g z)⁻¹) 0 := by
    simpa only [Pi.inv_apply] using (MeromorphicAt.inv (f := g) (x := 0) hg_meromorphic)
  have hsub_meromorphic : MeromorphicAt (fun z ↦ f z - a) 0 := by
    -- Inverting the reciprocal recovers `f - a`.
    simpa [g] using hg_inv_meromorphic
  have hf_meromorphic : MeromorphicAt f 0 := by
    -- Adding back the constant `a` preserves meromorphicity.
    exact
      (MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt₂
        (f := f) (g := fun _ : ℂ ↦ a) (x := 0) (MeromorphicAt.const a 0)).mp <| by
          simpa using hsub_meromorphic
  exact hess.not_meromorphicAt hf_meromorphic
