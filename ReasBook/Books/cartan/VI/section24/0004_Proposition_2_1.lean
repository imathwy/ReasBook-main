import Mathlib
import cartan.I.section03.«0012_Proposition_6_2»
import cartan.III.section10.«0009_Theorem_III_4_extra_7»
import cartan.VI.section22.«0005_Corollary_VI_1_extra_3»
import cartan.VI.section22.«0006_Definition_VI_1_extra_4»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set
open scoped Topology

-- Domain sampling note:
-- * source-facing layer: the proposition asserts that a planar simply connected domain is
--   biholomorphic to a bounded planar domain;
-- * core/canonical owner in this chapter: `HolomorphicIsomorph`;
-- * derived API discarded from the statement: openness of the target, the inverse-on-source data,
--   and the holomorphicity of both branches, all of which already come from that owner.

/-- Helper for Proposition 2.1: an injective analytic map on an open planar set cannot be
locally constant at a point of its domain. -/
private theorem simple_holomorphic_not_eventually_const_at
    {D : Set ℂ} {f : ℂ → ℂ} (_hf : AnalyticOnNhd ℂ f D) (h_simple : Set.InjOn f D)
    (hD_open : IsOpen D) {z : ℂ} (hz : z ∈ D) :
    ¬ ∀ᶠ w in 𝓝 z, f w = f z := by
  intro h_const
  have h_const_ne : ∀ᶠ w in 𝓝[≠] z, f w = f z :=
    h_const.filter_mono nhdsWithin_le_nhds
  -- Points in the punctured neighborhood stay in `D` and keep the same `f`-value.
  have h_witness :
      {w : ℂ | w ≠ z ∧ w ∈ D ∧ f w = f z} ∈ 𝓝[≠] z := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hD_open.mem_nhds hz),
      h_const_ne] with w hw_ne hwD hwf
    exact ⟨hw_ne, hwD, hwf⟩
  rcases Filter.nonempty_of_mem h_witness with ⟨w, hw_ne, hwD, hwf⟩
  exact hw_ne (h_simple hwD hz hwf)

/-- Helper for Proposition 2.1: an injective analytic map on an open planar set gives an open
embedding of the source subtype into `ℂ`. -/
private theorem simple_holomorphic_isOpenEmbedding
    {D : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D) (h_simple : Set.InjOn f D)
    (hD_open : IsOpen D) :
    Topology.IsOpenEmbedding (D.restrict f) := by
  have h_cont : Continuous (D.restrict f) := hf.continuousOn.restrict
  have h_inj : Function.Injective (D.restrict f) := h_simple.injective
  have h_open : IsOpenMap (D.restrict f) := by
    rw [isOpenMap_iff_nhds_le]
    intro z
    -- Apply the local open mapping theorem and exclude the locally constant branch by injectivity.
    have h_nhds : 𝓝 (f z.1) ≤ Filter.map f (𝓝 z.1) := by
      refine (hf z.1 z.2).eventually_constant_or_nhds_le_map_nhds_aux.resolve_left ?_
      exact simple_holomorphic_not_eventually_const_at hf h_simple hD_open z.2
    -- Rewrite the ambient neighborhood statement for the restricted source map.
    calc
      𝓝 ((D.restrict f) z) = 𝓝 (f z.1) := rfl
      _ ≤ Filter.map f (𝓝 z.1) := h_nhds
      _ = Filter.map f (Filter.map ((↑) : D → ℂ) (𝓝 z)) := by
        rw [← map_nhds_subtype_coe_eq_nhds z.2 (hD_open.mem_nhds z.2)]
      _ = Filter.map (D.restrict f) (𝓝 z) := by
        rw [Filter.map_map]
        rfl
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap h_cont h_inj h_open

/-- Helper for Proposition 2.1: the simply connected logarithm-branch theorem applied to
`z ↦ z - a` yields an analytic logarithm branch of `z - a` on `D`, and this branch is injective
because its exponential is exactly `z - a`. -/
private theorem exists_analytic_log_branch_sub_const
    {D : Set ℂ} (hD_open : IsOpen D) (hD_simply : IsSimplyConnected D) {a : ℂ} (ha : a ∉ D) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g D ∧
        Set.InjOn g D ∧
          Set.EqOn (Complex.exp ∘ g) (fun z ↦ z - a) D := by
  let m : ℂ → ℂ := fun z ↦ z - a
  have hm_cont : ContinuousOn m D := (continuous_id.sub continuous_const).continuousOn
  have hm_nonzero : (0 : ℂ) ∉ m '' D := by
    intro hz
    rcases hz with ⟨z, hzD, hzEq⟩
    have hzA : z = a := sub_eq_zero.mp <| by simpa [m] using hzEq
    exact ha (hzA ▸ hzD)
  rcases Complex.exists_continuousOn_eqOn_exp_comp hD_simply hD_open hm_cont hm_nonzero with
    ⟨F, hF_cont, hF_exp⟩
  let U : Set ℂ := m '' D
  let L : ℂ → ℂ := fun w ↦ F (w + a)
  have hU_open : IsOpen U := by
    let τ : ℂ ≃ₜ ℂ := Homeomorph.addRight (-a)
    -- The image of `D` under the translation `z ↦ z - a` is open.
    simpa [U, m, τ, sub_eq_add_neg] using τ.isOpenMap D hD_open
  have hU_connected : IsConnected U := by
    let τ : ℂ ≃ₜ ℂ := Homeomorph.addRight (-a)
    -- Translation preserves connectedness of the domain.
    simpa [U, m, τ, sub_eq_add_neg] using
      (τ.isConnected_image (s := D)).2 hD_simply.isPathConnected.isConnected
  have hshift_maps : MapsTo (fun w : ℂ ↦ w + a) U D := by
    intro w hw
    rcases hw with ⟨z, hz, rfl⟩
    simpa [m, sub_eq_add_neg, add_assoc] using hz
  have hL_cont : ContinuousOn L U := by
    -- Pull back the original continuous lift along the inverse translation `w ↦ w + a`.
    simpa [L] using hF_cont.comp (continuous_id.add continuous_const).continuousOn hshift_maps
  have hL_exp : Set.EqOn (Complex.exp ∘ L) id U := by
    intro w hw
    rcases hw with ⟨z, hz, rfl⟩
    -- On the translated image, the transported lift is a genuine logarithm branch.
    simpa [L, m, Function.comp, sub_eq_add_neg, add_assoc] using hF_exp hz
  have hL_branch : Complex.IsLogBranchOn L U := ⟨hU_open, hU_connected, hL_cont, hL_exp⟩
  have hL_analytic : AnalyticOnNhd ℂ L U := by
    -- A log branch on an open set is analytic because its derivative is `1 / w`.
    refine (Complex.analyticOnNhd_iff_differentiableOn hU_open).2 ?_
    intro w hw
    exact (hL_branch.hasDerivAt hw).differentiableAt.differentiableWithinAt
  have hm_analytic : AnalyticOnNhd ℂ m D := by
    -- The affine translation `z ↦ z - a` is holomorphic on every open set.
    refine (Complex.analyticOnNhd_iff_differentiableOn hD_open).2 ?_
    intro z hz
    simpa [m] using (differentiableAt_id.sub_const a).differentiableWithinAt
  let g : ℂ → ℂ := fun z ↦ L (m z)
  have hm_maps : MapsTo m D U := by
    intro z hz
    exact ⟨z, hz, rfl⟩
  have hg_analytic : AnalyticOnNhd ℂ g D := by
    -- Compose the analytic log branch on `U` with the translation `m`.
    simpa [g, m, Function.comp] using hL_analytic.comp hm_analytic hm_maps
  have hg_inj : Set.InjOn g D := by
    intro z₁ hz₁ z₂ hz₂ hEq
    -- Equality of branch values implies equality of their exponentials, hence equality of points.
    have hz_sub :
        z₁ - a = z₂ - a := by
      calc
        z₁ - a = Complex.exp (g z₁) := by
          symm
          simpa [g, m, Function.comp] using hL_exp ⟨z₁, hz₁, rfl⟩
        _ = Complex.exp (g z₂) := by rw [hEq]
        _ = z₂ - a := by
          simpa [g, m, Function.comp] using hL_exp ⟨z₂, hz₂, rfl⟩
    have hz_eq := congrArg (fun t : ℂ ↦ t + a) hz_sub
    simpa [sub_eq_add_neg, add_assoc] using hz_eq
  have hg_exp : Set.EqOn (Complex.exp ∘ g) (fun z ↦ z - a) D := by
    intro z hz
    -- The pulled-back branch still exponentiates to `z - a` on `D`.
    simpa [g, m, Function.comp] using hL_exp ⟨z, hz, rfl⟩
  exact ⟨g, hg_analytic, hg_inj, hg_exp⟩

/-- Helper for Proposition 2.1: an injective analytic map on an open domain contains a metric ball
around each image point inside its image. -/
private theorem exists_ball_subset_image_of_analytic_injOn
    {D : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D) (h_inj : Set.InjOn f D)
    (hD_open : IsOpen D) {z₀ : ℂ} (hz₀ : z₀ ∈ D) :
    ∃ r > 0, Metric.ball (f z₀) r ⊆ f '' D := by
  have hOpenMap : IsOpenMap (D.restrict f) :=
    (simple_holomorphic_isOpenEmbedding hf h_inj hD_open).isOpenMap
  have hOpenImage : IsOpen (f '' D) := by
    simpa [Set.range_restrict] using hOpenMap.isOpen_range
  have hz_mem : f z₀ ∈ f '' D := ⟨z₀, hz₀, rfl⟩
  -- Any open neighborhood of `f z₀` contains a ball centered at `f z₀`.
  exact Metric.mem_nhds_iff.mp (hOpenImage.mem_nhds hz_mem)

/-- Helper for Proposition 2.1: translating the image disc by the period `2π i` produces a ball
disjoint from the image of the logarithm branch. -/
private theorem translated_ball_disjoint_of_log_period
    {D : Set ℂ} {g : ℂ → ℂ} {a z₀ : ℂ} {r : ℝ}
    (hExp : Set.EqOn (Complex.exp ∘ g) (fun z ↦ z - a) D)
    (hball : Metric.ball (g z₀) r ⊆ g '' D) :
    Disjoint (Metric.ball (g z₀ + 2 * Real.pi * Complex.I) r) (g '' D) := by
  rw [Set.disjoint_left]
  intro w hwball hwimage
  rcases hwimage with ⟨z, hz, rfl⟩
  have hshift_ball : g z - 2 * Real.pi * Complex.I ∈ Metric.ball (g z₀) r := by
    -- Subtracting `2π i` from the center and the point preserves the radius.
    simpa [Metric.mem_ball, Complex.dist_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hwball
  rcases hball hshift_ball with ⟨z', hz', hz'_eq⟩
  have hz_period : g z = g z' + 2 * Real.pi * Complex.I := by
    -- The translated point and the original point differ by exactly one period.
    calc
      g z = (g z - 2 * Real.pi * Complex.I) + 2 * Real.pi * Complex.I := by simp
      _ = g z' + 2 * Real.pi * Complex.I := by rw [hz'_eq]
  have hExpEq : Complex.exp (g z) = Complex.exp (g z') := by
    -- Exponentials agree because `exp` is `2π i`-periodic.
    calc
      Complex.exp (g z) = Complex.exp (g z' + (1 : ℤ) * (2 * Real.pi * Complex.I)) := by
        simpa using congrArg Complex.exp hz_period
      _ = Complex.exp (g z') := by
        simpa using (Complex.exp_periodic.int_mul 1) (g z')
  have hz_sub :
      z - a = z' - a := by
    -- Compare exponentials with the defining identity `exp (g z) = z - a`.
    calc
      z - a = Complex.exp (g z) := by
        symm
        simpa [Function.comp] using hExp hz
      _ = Complex.exp (g z') := hExpEq
      _ = z' - a := by
        simpa [Function.comp] using hExp hz'
  have hzz' : z = z' := by
    have hz_eq := congrArg (fun t : ℂ ↦ t + a) hz_sub
    simpa [sub_eq_add_neg, add_assoc] using hz_eq
  have hsame : g z' = g z' + 2 * Real.pi * Complex.I := by
    simpa [hzz'] using hz_period
  have hzero : (0 : ℂ) = 2 * Real.pi * Complex.I := by
    -- Equal points in the image cannot differ by a nonzero period.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      congrArg (fun t : ℂ ↦ t - g z') hsame
  exact Complex.two_pi_I_ne_zero hzero.symm

/-- Helper for Proposition 2.1: an injective analytic map on an open set packages into the
chapter's `HolomorphicIsomorph` owner with target equal to its image. -/
private noncomputable def holomorphic_isomorph_of_analyticOnNhd_of_injOn_image
    {D : Set ℂ} {g : ℂ → ℂ} (hD_open : IsOpen D) (hg : AnalyticOnNhd ℂ g D)
    (hg_inj : Set.InjOn g D) :
    HolomorphicIsomorph D (g '' D) := by
  let e : OpenPartialHomeomorph ℂ ℂ :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict
      (hg_inj.toPartialEquiv g D)
      hg.continuousOn
      (simple_holomorphic_isOpenEmbedding hg hg_inj hD_open).isOpenMap
      hD_open
  refine ⟨e, ?_⟩
  refine
    { source_eq := ?_
      target_eq := ?_
      analyticOn_toFun := ?_
      analyticOn_symm := ?_ }
  · -- The ambient source is exactly the prescribed set `D`.
    simp [e]
  · -- The ambient target is the image `g '' D`.
    simp [e]
  · -- The forward branch is the original analytic map.
    simpa [e] using hg
  · -- The inverse branch is the analytic inverse-on-image from Corollary VI.1-extra-3.
    simpa [e, Set.range_restrict] using
      corollary_VI_1_extra_3_invFunOn_analyticOnNhd hg hg_inj hD_open

/-- Proposition 2.1: if `D ⊆ ℂ` is a proper simply connected open set satisfying the hypotheses
of the fundamental theorem, then `D` admits a holomorphic isomorphism to some bounded open set of
the complex plane. -/
theorem exists_biholomorphic_to_bounded_open_set {D : Set ℂ} (hD_open : IsOpen D)
    (hD_simplyConnected : IsSimplyConnected D) (hD_proper : D ≠ univ) :
    ∃ (Ω : Set ℂ) (e : HolomorphicIsomorph D Ω), Bornology.IsBounded Ω := by
  classical
  have ha_exists : ∃ a : ℂ, a ∉ D := by
    -- A proper subset of `ℂ` omits at least one point.
    have hnot_all : ¬ ∀ z : ℂ, z ∈ D := by
      simpa [Set.eq_univ_iff_forall] using hD_proper
    simpa using not_forall.mp hnot_all
  rcases ha_exists with ⟨a, ha⟩
  rcases exists_analytic_log_branch_sub_const hD_open hD_simplyConnected ha with
    ⟨g, hg_analytic, hg_inj, hExp⟩
  rcases hD_simplyConnected.nonempty with ⟨z₀, hz₀⟩
  rcases exists_ball_subset_image_of_analytic_injOn hg_analytic hg_inj hD_open hz₀ with
    ⟨r, hr_pos, hball⟩
  have hdisj := translated_ball_disjoint_of_log_period hExp hball
  let c : ℂ := g z₀ + 2 * Real.pi * Complex.I
  let h : ℂ → ℂ := fun z ↦ (g z - c)⁻¹
  have hsub_ne : ∀ z ∈ D, g z - c ≠ 0 :=
    sub_const_ne_zero_of_ball_disjoint (s := D) (f := g) (a := c) hr_pos hdisj
  have hh_analytic : AnalyticOnNhd ℂ h D := by
    -- The reciprocal of `g - c` is holomorphic because `g '' D` misses the translated ball.
    have hsub_analytic : AnalyticOnNhd ℂ (fun z ↦ g z - c) D := by
      simpa [c] using hg_analytic.sub analyticOnNhd_const
    simpa [h] using hsub_analytic.inv hsub_ne
  have hh_inj : Set.InjOn h D := by
    intro z₁ hz₁ z₂ hz₂ hEq
    -- The reciprocal preserves injectivity away from zero, so injectivity comes from `g`.
    have hsub_eq : g z₁ - c = g z₂ - c := inv_inj.mp hEq
    have hg_eq : g z₁ = g z₂ := by
      have hsum_eq := congrArg (fun t : ℂ ↦ t + c) hsub_eq
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum_eq
    exact hg_inj hz₁ hz₂ hg_eq
  let Ω : Set ℂ := h '' D
  let e : HolomorphicIsomorph D Ω :=
    holomorphic_isomorph_of_analyticOnNhd_of_injOn_image hD_open hh_analytic hh_inj
  have hΩ_subset : Ω ⊆ Metric.ball (0 : ℂ) (r⁻¹ + 1) := by
    intro w hw
    rcases hw with ⟨z, hz, rfl⟩
    have hnorm_le : ‖h z‖ ≤ r⁻¹ := by
      simpa [h, c] using
        norm_inv_sub_le_inv_radius_of_ball_disjoint (s := D) (f := g) (a := c) hr_pos hdisj z hz
    have hnorm_lt : ‖h z‖ < r⁻¹ + 1 := by
      linarith
    -- The reciprocal image therefore lies in a fixed Euclidean ball.
    simpa [Metric.mem_ball, Complex.dist_eq] using hnorm_lt
  have hΩ_bounded : Bornology.IsBounded Ω := by
    -- A subset of a bounded ball is bounded.
    exact Metric.isBounded_ball.subset hΩ_subset
  exact ⟨Ω, e, hΩ_bounded⟩
