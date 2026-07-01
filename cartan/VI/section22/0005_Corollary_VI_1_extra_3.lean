import Mathlib
import cartan.III.section11.«0009_Proposition_4_2»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set Complex
open scoped Topology

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so the owner search
-- was verified locally against mathlib's `Analysis/Complex/OpenMapping`,
-- `Analysis/Analytic/Inverse`, and the existing repo recall that "simple on `D`" is `Set.InjOn`.

variable {D : Set ℂ} {f : ℂ → ℂ}

/-- Helper for Corollary VI.1-extra-3: an injective analytic map on an open planar set is not
eventually constant at a point of the domain. -/
private theorem simple_holomorphic_not_eventually_const_at
    (_hf : AnalyticOnNhd ℂ f D) (h_simple : Set.InjOn f D) (hD_open : IsOpen D)
    {z : ℂ} (hz : z ∈ D) :
    ¬ ∀ᶠ w in 𝓝 z, f w = f z := by
  intro h_const
  have h_const_ne : ∀ᶠ w in 𝓝[≠] z, f w = f z :=
    h_const.filter_mono nhdsWithin_le_nhds
  -- On the punctured neighborhood, points stay in `D` and keep the same `f`-value.
  have h_witness :
      {w : ℂ | w ≠ z ∧ w ∈ D ∧ f w = f z} ∈ 𝓝[≠] z := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hD_open.mem_nhds hz),
      h_const_ne] with w hw_ne hwD hwf
    exact ⟨hw_ne, hwD, hwf⟩
  rcases Filter.nonempty_of_mem h_witness with ⟨w, hw_ne, hwD, hwf⟩
  exact hw_ne (h_simple hwD hz hwf)

private theorem simple_holomorphic_isOpenEmbedding
    (hf : AnalyticOnNhd ℂ f D) (h_simple : Set.InjOn f D) (hD_open : IsOpen D) :
    Topology.IsOpenEmbedding (D.restrict f) := by
  have h_cont : Continuous (D.restrict f) := hf.continuousOn.restrict
  have h_inj : Function.Injective (D.restrict f) := h_simple.injective
  have h_open : IsOpenMap (D.restrict f) := by
    rw [isOpenMap_iff_nhds_le]
    intro z
    -- Apply the local open mapping theorem in the ambient plane, using the helper above to
    -- eliminate the locally constant branch.
    have h_nhds : 𝓝 (f z.1) ≤ Filter.map f (𝓝 z.1) := by
      refine (hf z.1 z.2).eventually_constant_or_nhds_le_map_nhds_aux.resolve_left ?_
      exact simple_holomorphic_not_eventually_const_at hf h_simple hD_open z.2
    -- Rewrite the ambient neighborhood statement back to the restricted map on `D`.
    calc
      𝓝 ((D.restrict f) z) = 𝓝 (f z.1) := rfl
      _ ≤ Filter.map f (𝓝 z.1) := h_nhds
      _ = Filter.map f (Filter.map ((↑) : D → ℂ) (𝓝 z)) := by
        rw [← map_nhds_subtype_coe_eq_nhds z.2 (hD_open.mem_nhds z.2)]
      _ = Filter.map (D.restrict f) (𝓝 z) := by
        rw [Filter.map_map]
        rfl
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap h_cont h_inj h_open

private noncomputable def inducedOpenPartialHomeomorph
    (hf : AnalyticOnNhd ℂ f D) (h_simple : Set.InjOn f D) (hD_open : IsOpen D) :
    OpenPartialHomeomorph ℂ ℂ :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    (h_simple.toPartialEquiv f D)
    hf.continuousOn
    (simple_holomorphic_isOpenEmbedding hf h_simple hD_open).isOpenMap
    hD_open

/-- Corollary VI.1-extra-3 (1): if `f` is simple holomorphic on an open set `D`, then
`f` induces a homeomorphism from `D` onto its image `f '' D`. -/
noncomputable def corollary_VI_1_extra_3_homeomorph
    (hf : AnalyticOnNhd ℂ f D) (h_simple : Set.InjOn f D) (hD_open : IsOpen D) :
    D ≃ₜ (f '' D) :=
  (inducedOpenPartialHomeomorph hf h_simple hD_open).toHomeomorphSourceTarget

/-- The homeomorphism from `D` to `f '' D` acts on points by `f`. -/
theorem corollary_VI_1_extra_3_homeomorph_coe_apply
    (hf : AnalyticOnNhd ℂ f D) (h_simple : Set.InjOn f D) (hD_open : IsOpen D) (z : D) :
    ↑(corollary_VI_1_extra_3_homeomorph hf h_simple hD_open z) = f z := rfl

/-- Helper for Corollary VI.1-extra-3: if the derivative vanishes at `z`, then the shifted function
`w ↦ f w - f z` has analytic order at least `2` at `z`. -/
private theorem analyticOrderAt_sub_two_le_of_deriv_zero
    (hf : AnalyticOnNhd ℂ f D) {z : ℂ} (hz : z ∈ D) (hderiv : deriv f z = 0) :
    (2 : ℕ∞) ≤ analyticOrderAt (fun w ↦ f w - f z) z := by
  -- The zeroth and first iterated derivatives vanish for the shifted function at `z`.
  have hz_analytic : AnalyticAt ℂ (fun w ↦ f w - f z) z := (hf z hz).sub analyticAt_const
  change (2 : ℕ) ≤ analyticOrderAt (fun w ↦ f w - f z) z
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hz_analytic]
  intro i hi
  have hi' : i = 0 ∨ i = 1 := by omega
  cases hi' with
  | inl h0 =>
      simp [h0, iteratedDeriv_zero]
  | inr h1 =>
      simp [h1, iteratedDeriv_one, hderiv]

/-- Helper for Corollary VI.1-extra-3: a simple holomorphic map on an open planar domain has
nonvanishing derivative at every point of the domain. -/
private theorem simple_holomorphic_deriv_ne_zero_at
    (hf : AnalyticOnNhd ℂ f D) (h_simple : Set.InjOn f D) (hD_open : IsOpen D)
    {z : ℂ} (hz : z ∈ D) :
    deriv f z ≠ 0 := by
  intro hderiv
  -- Route correction: rather than rebuilding a local factorization argument here, use the
  -- packaged multiplicity theorem from Proposition III.4.2 to contradict injectivity.
  have htwo :
      (2 : ℕ∞) ≤ analyticOrderAt (fun w ↦ f w - f z) z :=
    analyticOrderAt_sub_two_le_of_deriv_zero hf hz hderiv
  have hnot_top : analyticOrderAt (fun w ↦ f w - f z) z ≠ ⊤ := by
    intro htop
    obtain ⟨c, hc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.mp <|
      (eventuallyConst_iff_analyticOrderAt_sub_eq_top).2 htop
    have hcz : c = f z := by
      simpa using (hc.self_of_nhds).symm
    exact simple_holomorphic_not_eventually_const_at hf h_simple hD_open hz <|
      by simpa [hcz] using hc
  let k : ℕ := analyticOrderNatAt (fun w ↦ f w - f z) z
  have hk : analyticOrderAt (fun w ↦ f w - f z) z = k := by
    rw [← Nat.cast_analyticOrderNatAt hnot_top]
  have hk_two : 2 ≤ k := by
    have htwo' : (2 : ℕ∞) ≤ (k : ℕ∞) := by simpa [hk] using htwo
    exact_mod_cast htwo'
  have hk_pos : 0 < k := by omega
  obtain ⟨rD, hrD_pos, hrD_subset⟩ := Metric.mem_nhds_iff.mp (hD_open.mem_nhds hz)
  obtain ⟨r₀, hr₀_pos, hr₀⟩ :=
    nearby_level_set_has_k_simple_roots (f := f) (z₀ := z) (a := f z) (k := k) hk_pos hk
  let r : ℝ := min rD r₀
  have hr_pos : 0 < r := by
    exact lt_min hrD_pos hr₀_pos
  have hr_le : r ≤ r₀ := min_le_right _ _
  have hr_subset : Metric.ball z r ⊆ D := by
    intro w hw
    exact hrD_subset (by
      simpa [Metric.mem_ball, r] using (lt_of_lt_of_le hw (min_le_left rD r₀)))
  obtain ⟨δ, hδ_pos, hδ⟩ := hr₀ r hr_pos hr_le
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  let b : ℂ := f z + (((δ / 2 : ℝ) : ℂ))
  have hb_sub : b - f z = (((δ / 2 : ℝ) : ℂ)) := by
    simp [b]
  have hhalf_norm : ‖(((δ / 2 : ℝ) : ℂ))‖ = δ / 2 := by
    simp [Complex.norm_real, hδ_nonneg]
  have hb_dist : ‖b - f z‖ < δ := by
    rw [hb_sub, hhalf_norm]
    linarith
  have hhalf_ne : (((δ / 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (half_pos hδ_pos))
  have hb_ne : b ≠ f z := by
    intro hb_eq
    have hzero : b - f z = 0 := sub_eq_zero.mpr hb_eq
    exact hhalf_ne (by simpa [hb_sub] using hzero)
  obtain ⟨hfiber, -⟩ := hδ b hb_dist hb_ne
  have hfiber_le_one :
      {w : ℂ | w ∈ Metric.ball z r ∧ f w = b}.encard ≤ 1 := by
    refine (Set.encard_le_one_iff_subsingleton.2 ?_)
    intro w₁ hw₁ w₂ hw₂
    apply h_simple
    · exact hr_subset hw₁.1
    · exact hr_subset hw₂.1
    · exact hw₁.2.trans hw₂.2.symm
  have hk_le_one_enat : (k : ℕ∞) ≤ 1 := by
    rw [← hfiber]
    exact hfiber_le_one
  have hk_le_one : k ≤ 1 := by
    exact_mod_cast hk_le_one_enat
  omega

/-- Helper for Corollary VI.1-extra-3: the inverse branch `Function.invFunOn f D` is analytic at
each point of the image `f '' D`. -/
private theorem invFunOn_analyticAt_image_point
    (hf : AnalyticOnNhd ℂ f D) (h_simple : Set.InjOn f D) (hD_open : IsOpen D)
    {y : ℂ} (hy : y ∈ f '' D) :
    AnalyticAt ℂ (Function.invFunOn f D) y := by
  let e := inducedOpenPartialHomeomorph hf h_simple hD_open
  have hy_target : y ∈ e.target := by
    simpa [e, inducedOpenPartialHomeomorph] using hy
  have hz_source : e.symm y ∈ e.source := by
    simpa using (e : OpenPartialHomeomorph ℂ ℂ).map_target hy_target
  have hzD : e.symm y ∈ D := by
    simpa [e, inducedOpenPartialHomeomorph] using hz_source
  -- The forward branch is analytic at the preimage point, and the previous helper removes
  -- ramification there.
  have hforward : AnalyticAt ℂ e (e.symm y) := by
    simpa [e, inducedOpenPartialHomeomorph] using hf (e.symm y) hzD
  have hderiv_ne : deriv f (e.symm y) ≠ 0 :=
    simple_holomorphic_deriv_ne_zero_at hf h_simple hD_open hzD
  let i : ℂ ≃L[ℂ] ℂ :=
    ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv f (e.symm y)) hderiv_ne)
  have hfd :
      fderiv ℂ e (e.symm y) = i := by
    have hfd' : HasFDerivAt e (i : ℂ →L[ℂ] ℂ) (e.symm y) := by
      simpa [e, i, inducedOpenPartialHomeomorph] using
        (((hf (e.symm y) hzD).hasStrictDerivAt.hasStrictFDerivAt_equiv hderiv_ne).hasFDerivAt)
    exact hfd'.fderiv
  simpa [e, inducedOpenPartialHomeomorph] using e.analyticAt_symm hy_target hforward hfd

/-- Corollary VI.1-extra-3 (2): for a simple holomorphic function on an open set `D`, the
inverse map on `f '' D`, represented by `Function.invFunOn f D`, is holomorphic on `f '' D`. -/
theorem corollary_VI_1_extra_3_invFunOn_analyticOnNhd
    (hf : AnalyticOnNhd ℂ f D) (h_simple : Set.InjOn f D) (hD_open : IsOpen D) :
    AnalyticOnNhd ℂ (Function.invFunOn f D) (f '' D) := by
  intro y hy
  -- The pointwise inverse-function theorem closes the global analyticity statement.
  exact invFunOn_analyticAt_image_point hf h_simple hD_open hy
