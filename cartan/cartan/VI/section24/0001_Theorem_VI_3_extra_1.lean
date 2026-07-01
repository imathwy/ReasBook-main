import Mathlib
import cartan.I.section04.«0010_Corollary_1»
import cartan.V.section18.«0004_Theorem_1»
import cartan.V.section18.«0006_Theorem_2»
import cartan.V.section18.«0011_Proposition_2_2»
import cartan.V.section18.«0012_Proposition_3_1»
import cartan.V.section18.«0014_Remark_V_1_extra_8»
import cartan.V.section21.«0001_Definition_V_4_extra_1»
import cartan.V.section21.«0002_Proposition_1_1»
import cartan.V.section21.«0005_Theorem_V_4_extra_3»
import cartan.VI.section22.«0006_Definition_VI_1_extra_4»
import cartan.VI.section24.«0004_Proposition_2_1»
import cartan.VI.section24.«0005_Proposition_3_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set
open scoped Topology

/-- Helper for Theorem VI.3-extra-1: the open unit disc is simply connected. -/
theorem unitDisc_isSimplyConnected : IsSimplyConnected (Metric.ball (0 : ℂ) 1) := by
  -- Transfer contractibility from `ℂ` to the open unit disc along the standard homeomorphism.
  change SimplyConnectedSpace (Metric.ball (0 : ℂ) 1)
  let _ : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
    ((Homeomorph.unitBall : ℂ ≃ₜ Metric.ball (0 : ℂ) 1)).contractibleSpace_iff.mp inferInstance
  infer_instance

/-- Helper for Theorem VI.3-extra-1: the open unit disc is a proper subset of `ℂ`. -/
theorem unitDisc_ne_univ : Metric.ball (0 : ℂ) 1 ≠ univ := by
  -- The point `2` cannot belong to the unit disc.
  intro hball
  have htwo : (2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp [hball]
  norm_num [mem_ball_zero_iff] at htwo

namespace HolomorphicIsomorph

variable {D D' D'' : Set ℂ}

/-- Helper for Theorem VI.3-extra-1: a holomorphic isomorphism maps its prescribed source into
its prescribed target. -/
theorem mapsTo (e : HolomorphicIsomorph D D') :
    MapsTo e D D' := by
  -- Rewrite source membership to the underlying partial-homeomorphism source.
  intro z hz
  have hz_source : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
    simpa [e.source_eq] using hz
  -- Then transport the image back through the prescribed target equality.
  simpa [e.target_eq] using (e : OpenPartialHomeomorph ℂ ℂ).map_source hz_source

/-- Helper for Theorem VI.3-extra-1: holomorphic isomorphisms compose by composing their
underlying open partial homeomorphisms. -/
noncomputable def trans (e : HolomorphicIsomorph D D') (e' : HolomorphicIsomorph D' D'') :
    HolomorphicIsomorph D D'' := by
  refine ⟨(e : OpenPartialHomeomorph ℂ ℂ).trans (e' : OpenPartialHomeomorph ℂ ℂ), ?_⟩
  refine
    { source_eq := ?_
      target_eq := ?_
      analyticOn_toFun := ?_
      analyticOn_symm := ?_ }
  · -- The composed source is all of `D` because `e` already lands in `D'`.
    ext z
    constructor
    · intro hz
      rw [OpenPartialHomeomorph.trans_source] at hz
      simpa [e.source_eq] using hz.1
    · intro hz
      have hz_source : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
        simpa [e.source_eq] using hz
      have hez_source : e z ∈ (e' : OpenPartialHomeomorph ℂ ℂ).source := by
        simpa [e.target_eq, e'.source_eq] using
          (e : OpenPartialHomeomorph ℂ ℂ).map_source hz_source
      rw [OpenPartialHomeomorph.trans_source]
      exact ⟨hz_source, hez_source⟩
  · -- Dually, the composed target is all of `D''`.
    ext z
    constructor
    · intro hz
      rw [OpenPartialHomeomorph.trans_target] at hz
      simpa [e'.target_eq] using hz.1
    · intro hz
      have hz_target : z ∈ (e' : OpenPartialHomeomorph ℂ ℂ).target := by
        simpa [e'.target_eq] using hz
      have hpre_target :
          (e' : OpenPartialHomeomorph ℂ ℂ).symm z ∈ (e : OpenPartialHomeomorph ℂ ℂ).target := by
        simpa [e.target_eq, e'.source_eq] using
          (e' : OpenPartialHomeomorph ℂ ℂ).map_target hz_target
      rw [OpenPartialHomeomorph.trans_target]
      exact ⟨hz_target, hpre_target⟩
  · -- The forward branch is the usual composition `e' ∘ e`.
    simpa using e'.analyticOn_toFun.comp e.analyticOn_toFun e.mapsTo
  · -- The inverse branch is the reverse composition of the inverse branches.
    have hsymm_maps :
        MapsTo ((e' : OpenPartialHomeomorph ℂ ℂ).symm : ℂ → ℂ) D'' D' := by
      intro z hz
      have hz_target : z ∈ (e' : OpenPartialHomeomorph ℂ ℂ).target := by
        simpa [e'.target_eq] using hz
      simpa [e'.source_eq] using (e' : OpenPartialHomeomorph ℂ ℂ).map_target hz_target
    simpa using e.analyticOn_invFun.comp e'.analyticOn_invFun hsymm_maps

end HolomorphicIsomorph

/-- Helper for Theorem VI.3-extra-1: after Proposition 2.1 one may replace a proper simply
connected open set by a biholomorphic model that contains `0` and lies in the unit disc. -/
theorem exists_centered_subdisc_model {D : Set ℂ}
    (hD_open : IsOpen D) (hD_simplyConnected : IsSimplyConnected D) (hD_proper : D ≠ univ) :
    ∃ (Δ : Set ℂ) (_e : HolomorphicIsomorph D Δ),
      IsOpen Δ ∧ IsSimplyConnected Δ ∧
        (0 : ℂ) ∈ Δ ∧ Δ ⊆ Metric.ball (0 : ℂ) 1 := by
  rcases exists_biholomorphic_to_bounded_open_set hD_open hD_simplyConnected hD_proper with
    ⟨Ω, eΩ, hΩ_bounded⟩
  have hΩ_open : IsOpen Ω := eΩ.isOpen_target
  have hΩ_simply : IsSimplyConnected Ω := by
    -- Transport simple connectedness across the homeomorphism underlying `eΩ`.
    let _ : SimplyConnectedSpace D := hD_simplyConnected.simplyConnectedSpace
    exact eΩ.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  rcases hΩ_simply.nonempty with ⟨a, ha⟩
  have hΩ_bound :
      ∃ R > 0, ∀ z ∈ Ω, ‖z‖ < R := by
    simpa using hΩ_bounded.exists_pos_norm_lt
  rcases hΩ_bound with ⟨R, hR_pos, hR⟩
  let ρ : ℝ := R + ‖a‖ + 1
  have hρ_pos : 0 < ρ := by
    positivity
  have hρ_ne : ((ρ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hρ_pos.ne'
  let τ : ℂ ≃ₜ ℂ :=
    (Homeomorph.addRight (-a)).trans
      (Homeomorph.mulRight₀ (((ρ : ℝ) : ℂ)⁻¹) (inv_ne_zero hρ_ne))
  let Δ : Set ℂ := τ '' Ω
  let eτ : OpenPartialHomeomorph ℂ ℂ := τ.toOpenPartialHomeomorphOfImageEq Ω hΩ_open Δ rfl
  have hΔ_open : IsOpen Δ := by
    -- The affine image of an open set is open.
    simpa [eτ, Δ] using eτ.open_target
  have hΔ_simply : IsSimplyConnected Δ := by
    -- Simple connectedness is preserved by ambient homeomorphisms.
    simpa [Δ] using (τ.isSimplyConnected_image (s := Ω)).2 hΩ_simply
  have h0Δ : (0 : ℂ) ∈ Δ := by
    -- The chosen center `a` is sent to `0`.
    refine ⟨a, ha, ?_⟩
    change τ a = 0
    simp [τ, Homeomorph.trans_apply]
  have hΔ_subset : Δ ⊆ Metric.ball (0 : ℂ) 1 := by
    -- The scale `ρ > R + ‖a‖` forces the translated image strictly inside the unit disc.
    rintro w ⟨z, hz, rfl⟩
    have hz_norm : ‖z‖ < R := hR z hz
    have hza_lt : ‖z - a‖ < ρ := by
      calc
        ‖z - a‖ = ‖z + -a‖ := by simp [sub_eq_add_neg]
        _ ≤ ‖z‖ + ‖-a‖ := norm_add_le _ _
        _ = ‖z‖ + ‖a‖ := by rw [norm_neg]
        _ < R + ‖a‖ + 1 := by linarith
    have hw_norm : ‖(z - a) / ((ρ : ℝ) : ℂ)‖ < 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ_pos]
      exact (div_lt_one hρ_pos).2 hza_lt
    simpa [Δ, τ, Homeomorph.trans_apply, mem_ball_zero_iff, div_eq_mul_inv, sub_eq_add_neg] using
      hw_norm
  have hτ_analytic : AnalyticOnNhd ℂ (τ : ℂ → ℂ) Ω := by
    -- The forward affine map is holomorphic on every open set.
    have hdiff :
        DifferentiableOn ℂ (fun z : ℂ ↦ (z - a) / (((ρ : ℝ) : ℂ))) Ω := by
      intro z hz
      simpa [div_eq_mul_inv, sub_eq_add_neg] using
        ((differentiableAt_id.sub_const a).mul_const ((((ρ : ℝ) : ℂ)⁻¹))).differentiableWithinAt
    simpa [τ, Homeomorph.trans_apply, div_eq_mul_inv, sub_eq_add_neg] using
      (Complex.analyticOnNhd_iff_differentiableOn hΩ_open).2 hdiff
  have hτsymm_analytic : AnalyticOnNhd ℂ (τ.symm : ℂ → ℂ) Δ := by
    -- The inverse affine map is holomorphic on the image set as well.
    have hdiff :
        DifferentiableOn ℂ (fun w : ℂ ↦ w * (((ρ : ℝ) : ℂ)) + a) Δ := by
      intro w hw
      simpa using
        ((differentiableAt_id.mul_const (((ρ : ℝ) : ℂ))).add_const a).differentiableWithinAt
    have hsymm_eq :
        Set.EqOn (τ.symm : ℂ → ℂ) (fun w : ℂ ↦ w * (((ρ : ℝ) : ℂ)) + a) Δ := by
      intro w hw
      simp [τ, Homeomorph.addRight, Homeomorph.mulRight₀]
    exact AnalyticOnNhd.congr hΔ_open
      ((Complex.analyticOnNhd_iff_differentiableOn hΔ_open).2 hdiff) hsymm_eq.symm
  let eAffine : HolomorphicIsomorph Ω Δ :=
    ⟨eτ,
      { source_eq := rfl
        target_eq := rfl
        analyticOn_toFun := hτ_analytic
        analyticOn_symm := hτsymm_analytic }⟩
  -- Compose the bounded-model biholomorphism with the affine normalization.
  exact ⟨Δ, eΩ.trans eAffine, hΔ_open, hΔ_simply, h0Δ, hΔ_subset⟩

/-- Helper for Theorem VI.3-extra-1: on any domain contained in the unit disc, the identity map is
already a normalized univalent disc map. -/
theorem id_isNormalizedUnivalentDiscMapOn {Δ : Set ℂ}
    (hΔ_subset : Δ ⊆ Metric.ball (0 : ℂ) 1) :
    IsNormalizedUnivalentDiscMapOn Δ (fun z : ℂ ↦ z) := by
  constructor
  · -- The identity map is injective on every set.
    intro z hz w hw hzw
    simpa using hzw
  constructor
  · -- Holomorphicity is the standard analyticity of the identity.
    simpa using (analyticOnNhd_id : AnalyticOnNhd ℂ (fun z : ℂ ↦ z) Δ)
  constructor
  · -- The normalization condition is immediate.
    rfl
  · -- The target condition is exactly the domain inclusion into the unit disc.
    simpa using hΔ_subset

/-- Helper for Theorem VI.3-extra-1: a locally uniform limit of admissible normalized maps is again
admissible, because normalization, injectivity, and the derivative lower bound all persist in the
limit. -/
theorem admissible_limit_of_tendsto_locally_uniformly {Δ : Set ℂ}
    (hΔ_open : IsOpen Δ) (hΔ_simply : IsSimplyConnected Δ) (h0Δ : (0 : ℂ) ∈ Δ)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, IsNormalizedUnivalentDiscMapOn Δ (F n))
    (hF_deriv : ∀ n, 1 ≤ ‖deriv (F n) 0‖)
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop Δ) :
    IsNormalizedUnivalentDiscMapOn Δ f ∧ 1 ≤ ‖deriv f 0‖ := by
  have hΔ_preconnected : IsPreconnected Δ := hΔ_simply.isPathConnected.isConnected.isPreconnected
  have hF_diff : ∀ n, DifferentiableOn ℂ (F n) Δ := fun n ↦ (hF n).differentiableOn
  have hf_diff : DifferentiableOn ℂ f Δ :=
    differentiableOn_of_tendsto_locally_uniformly_on_compacts hΔ_open hF_diff hconv
  have hf_analytic : AnalyticOnNhd ℂ f Δ := by
    -- On an open domain, differentiability on the domain is equivalent to analyticity there.
    exact (Complex.analyticOnNhd_iff_differentiableOn hΔ_open).2 hf_diff
  have hf_zero : f 0 = 0 := by
    -- Evaluate the locally uniform convergence at the normalized center.
    have hzero_tendsto : Tendsto (fun n ↦ F n 0) atTop (𝓝 (f 0)) := hconv.tendsto_at h0Δ
    have hzero_const : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (𝓝 (f 0)) := by
      simpa [Function.comp, funext fun n ↦ (hF n).map_zero] using hzero_tendsto
    have hmem : f 0 ∈ ({0} : Set ℂ) := by
      refine isClosed_singleton.mem_of_tendsto hzero_const ?_
      exact Filter.Eventually.of_forall fun _ ↦ by simp
    simpa using hmem
  have hderiv_tendsto :
      Tendsto (fun n ↦ deriv (F n) 0) atTop (𝓝 (deriv f 0)) := by
    -- Derivatives converge locally uniformly as well, hence in particular at the center.
    exact
      (tendsto_locally_uniformly_on_compacts_deriv hΔ_open hF_diff hconv).tendsto_at h0Δ
  have hderiv_norm_tendsto :
      Tendsto (fun n ↦ ‖deriv (F n) 0‖) atTop (𝓝 ‖deriv f 0‖) :=
    continuous_norm.tendsto _ |>.comp hderiv_tendsto
  have hf_deriv : 1 ≤ ‖deriv f 0‖ := by
    -- The inequality survives because `[1, ∞)` is closed in `ℝ`.
    exact isClosed_Ici.mem_of_tendsto hderiv_norm_tendsto <|
      Filter.Eventually.of_forall fun n ↦ hF_deriv n
  have hf_not_const : ¬ ∃ c : ℂ, Set.EqOn f (fun _ ↦ c) Δ := by
    -- A constant limit would force the derivative at `0` to vanish, contradicting `hf_deriv`.
    intro hconst
    rcases hconst with ⟨c, hc⟩
    have hconst_nhds : f =ᶠ[𝓝 (0 : ℂ)] fun _ : ℂ ↦ c :=
      Set.EqOn.eventuallyEq_of_mem hc (hΔ_open.mem_nhds h0Δ)
    have hderiv_zero : deriv f 0 = deriv (fun _ : ℂ ↦ c) 0 := by
      simpa using hconst_nhds.deriv_eq
    have hnorm_zero : ‖deriv f 0‖ = 0 := by
      simpa using congrArg norm hderiv_zero
    have : ¬ (1 : ℝ) ≤ 0 := by norm_num
    exact this (hnorm_zero ▸ hf_deriv)
  have hf_inj : Set.InjOn f Δ :=
    injOn_of_tendsto_locally_uniformly_on_compacts_of_not_eqOn_const
      hΔ_open hΔ_preconnected hF_diff hconv (fun n ↦ (hF n).injOn) hf_not_const
  have hf_maps_closed : MapsTo f Δ (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    -- Pointwise convergence preserves the closed unit-ball bound.
    have hz_tendsto : Tendsto (fun n ↦ F n z) atTop (𝓝 (f z)) := hconv.tendsto_at hz
    have hnorm_tendsto :
        Tendsto (fun n ↦ ‖F n z‖) atTop (𝓝 ‖f z‖) :=
      continuous_norm.tendsto _ |>.comp hz_tendsto
    have hclosed_norm : ‖f z‖ ∈ Set.Iic (1 : ℝ) := by
      refine isClosed_Iic.mem_of_tendsto hnorm_tendsto ?_
      exact Filter.Eventually.of_forall fun n ↦ (mem_ball_zero_iff.mp ((hF n).mapsTo hz)).le
    simpa [mem_closedBall_zero_iff] using hclosed_norm
  have hf_image_open : IsOpen (f '' Δ) := by
    -- The nonconstant holomorphic limit is an open map on the connected open domain.
    rcases hf_analytic.is_constant_or_isOpen hΔ_preconnected with hconst | hopen
    · exact (hf_not_const hconst).elim
    · exact hopen Δ (Subset.refl Δ) hΔ_open
  have hf_maps : MapsTo f Δ (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hz_image : f z ∈ f '' Δ := ⟨z, hz, rfl⟩
    have himage_subset :
        f '' Δ ⊆ Metric.closedBall (0 : ℂ) 1 := by
      rintro w ⟨w0, hw0, rfl⟩
      exact hf_maps_closed hw0
    have hz_interior :
        f z ∈ interior (Metric.closedBall (0 : ℂ) 1) :=
      interior_maximal himage_subset hf_image_open hz_image
    simpa [interior_closedBall' (0 : ℂ) 1] using hz_interior
  exact ⟨⟨hf_inj, hf_analytic, hf_zero, hf_maps⟩, hf_deriv⟩

/-- Helper for Theorem VI.3-extra-1: the source family `B` consists of those holomorphic
restrictions coming from normalized univalent maps on `Δ` whose derivative norm at `0` is at least
`1`. This matches the source proof's compactness argument. -/
def normalized_disc_admissible_family (Δ : Set ℂ) : Set (analyticFunctionSubring ℂ Δ) :=
  {u | ∃ f : ℂ → ℂ, IsNormalizedUnivalentDiscMapOn Δ f ∧ 1 ≤ ‖deriv f 0‖ ∧ Δ.restrict f = u}

/-- Helper for Theorem VI.3-extra-1: on an open set containing `0`, the derivative at `0` depends
only on the restriction of a holomorphic map to that set. -/
theorem deriv_eq_of_restrict_eq {Δ : Set ℂ}
    (hΔ_open : IsOpen Δ) (h0Δ : (0 : ℂ) ∈ Δ) {f g : ℂ → ℂ}
    (hfg : Δ.restrict f = Δ.restrict g) :
    deriv f 0 = deriv g 0 := by
  -- Equality of restrictions gives equality on a neighborhood of `0`, so derivatives agree there.
  have hEqOn : Set.EqOn f g Δ := by
    intro z hz
    have hz_eval := congrArg (fun h : Δ → ℂ ↦ h ⟨z, hz⟩) hfg
    simpa using hz_eval
  have hEq_nhds : f =ᶠ[𝓝 (0 : ℂ)] g :=
    Set.EqOn.eventuallyEq_of_mem hEqOn (hΔ_open.mem_nhds h0Δ)
  simpa using hEq_nhds.deriv_eq

/-- Helper for Theorem VI.3-extra-1: the identity map shows that the admissible family `B` is
nonempty as soon as `Δ` lies in the unit disc. -/
theorem normalized_disc_admissible_family_nonempty {Δ : Set ℂ}
    (hΔ_subset : Δ ⊆ Metric.ball (0 : ℂ) 1) :
    (normalized_disc_admissible_family Δ).Nonempty := by
  let u : analyticFunctionSubring ℂ Δ :=
    ⟨Δ.restrict (fun z : ℂ ↦ z), ⟨fun z : ℂ ↦ z, analyticOnNhd_id, rfl⟩⟩
  refine ⟨u, ?_⟩
  refine ⟨fun z : ℂ ↦ z, id_isNormalizedUnivalentDiscMapOn hΔ_subset, ?_, rfl⟩
  -- The source proof starts from the identity, whose derivative at `0` has norm `1`.
  simp [deriv_id'']

/-- Helper for Theorem VI.3-extra-1: every admissible function maps `Δ` into the unit disc, so the
whole family has the common compact-subset bound `1`. This is the boundedness input in the source
compactness argument, written without introducing extra compact-open infrastructure. -/
theorem normalized_disc_admissible_family_norm_le_one_on_compact {Δ K : Set ℂ}
    (hKΔ : K ⊆ Δ) :
    ∀ u ∈ normalized_disc_admissible_family Δ,
      ∀ z : K, ‖u ⟨z, hKΔ z.2⟩‖ ≤ 1 := by
  intro u hu z
  rcases hu with ⟨f, hf, -, hu_eq⟩
  -- Each admissible member already lands in the unit disc on all of `Δ`.
  rw [← hu_eq]
  simpa [mem_ball_zero_iff] using (mem_ball_zero_iff.mp (hf.mapsTo (hKΔ z.2))).le

/-- Helper for Theorem VI.3-extra-1: the admissible family `B` is uniformly bounded on compact
subsets of `Δ` by the common unit-disc bound from the source proof. -/
theorem normalized_disc_admissible_family_uniformlyBoundedOnCompacta {Δ : Set ℂ} :
    UniformlyBoundedOnCompacta Δ (normalized_disc_admissible_family Δ) := by
  intro K _ hKΔ
  -- The source argument uses the same bound `1` on every compact subset of `Δ`.
  refine ⟨1, ?_⟩
  intro u hu z hz
  exact normalized_disc_admissible_family_norm_le_one_on_compact (K := K) hKΔ u hu ⟨z, hz⟩

/-- Helper for Theorem VI.3-extra-1: the admissible family `B` is closed in the compact-open
topology on `C(Δ, ℂ)`. The proof follows the source route: compact-open convergence gives locally
uniform convergence on `Δ`, and the earlier admissible-limit lemma keeps the limit inside `B`. -/
theorem normalized_disc_admissible_family_isClosed {Δ : Set ℂ}
    (hΔ_open : IsOpen Δ) (hΔ_simply : IsSimplyConnected Δ) (h0Δ : (0 : ℂ) ∈ Δ) :
    IsClosed
      (((↑) : analyticFunctionSubring ℂ Δ → C(Δ, ℂ)) ''
        normalized_disc_admissible_family Δ) := by
  classical
  letI : LocallyCompactSpace Δ := hΔ_open.locallyCompactSpace
  letI := continuousMap_metrizable_preconditions_of_isOpen (X := ℂ) (E := ℂ) Δ hΔ_open
  rw [isClosed_iff_seq_limit_mem]
  intro u v hv hconv
  choose w hw using hv
  have hw_mem : ∀ n, w n ∈ normalized_disc_admissible_family Δ := fun n ↦ (hw n).1
  have hw_coe : ∀ n, ((w n : analyticFunctionSubring ℂ Δ) : C(Δ, ℂ)) = v n := fun n ↦ (hw n).2
  choose F hF using hw_mem
  have hF_admissible : ∀ n, IsNormalizedUnivalentDiscMapOn Δ (F n) := fun n ↦ (hF n).1
  have hF_deriv : ∀ n, 1 ≤ ‖deriv (F n) 0‖ := fun n ↦ (hF n).2.1
  have hF_restrict : ∀ n, Δ.restrict (F n) = w n := fun n ↦ (hF n).2.2
  let f : ℂ → ℂ := fun z ↦ if hz : z ∈ Δ then u ⟨z, hz⟩ else 0
  have hw_tendsto :
      Tendsto (fun n ↦ ((w n : analyticFunctionSubring ℂ Δ) : C(Δ, ℂ))) atTop (𝓝 u) := by
    -- Replace the chosen representatives by the original convergent sequence in `C(Δ, ℂ)`.
    refine Tendsto.congr' ?_ hconv
    exact Filter.Eventually.of_forall fun n ↦ (hw_coe n).symm
  have hloc :
      TendstoLocallyUniformlyOn F f atTop Δ := by
    -- Convert compact-open convergence on the subtype `Δ` to locally uniform convergence on `Δ`.
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    let hw_loc :
        TendstoLocallyUniformly (fun n (x : Δ) ↦ (w n : C(Δ, ℂ)) x) u atTop :=
      (ContinuousMap.tendsto_iff_tendstoLocallyUniformly).1 hw_tendsto
    have hF_loc : TendstoLocallyUniformly (fun n (x : Δ) ↦ F n x) u atTop := by
      exact hw_loc.congr (fun n x ↦ by
        have hx : Δ.restrict (F n) x = (w n : analyticFunctionSubring ℂ Δ) x :=
          congrArg (fun g : Δ → ℂ ↦ g x) (hF_restrict n)
        simpa using hx.symm)
    exact hF_loc.congr_right (fun x ↦ by simp [f])
  have hlimit :
      IsNormalizedUnivalentDiscMapOn Δ f ∧ 1 ≤ ‖deriv f 0‖ :=
    admissible_limit_of_tendsto_locally_uniformly hΔ_open hΔ_simply h0Δ hF_admissible hF_deriv hloc
  let uf : analyticFunctionSubring ℂ Δ :=
    ⟨Δ.restrict f, ⟨f, hlimit.1.analyticOnNhd, rfl⟩⟩
  have huf_mem : uf ∈ normalized_disc_admissible_family Δ := by
    -- The admissible-limit lemma rebuilds the source family conditions for the limit.
    exact ⟨f, hlimit.1, hlimit.2, rfl⟩
  refine ⟨uf, huf_mem, ?_⟩
  -- The resulting restriction agrees with the limit function already living in `C(Δ, ℂ)`.
  ext z
  change Δ.restrict f z = u z
  simp [f]

/-- Helper for Theorem VI.3-extra-1: on an open planar domain, a holomorphic family that is
uniformly bounded on compacta has compact closure in the compact-open function space. -/
theorem holomorphic_family_closure_isCompact_of_uniformlyBoundedOnCompacta
    {D : Set ℂ} (hD_open : IsOpen D) {A : Set (analyticFunctionSubring ℂ D)}
    (hA : UniformlyBoundedOnCompacta D A) :
    IsCompact (closure (((↑) : analyticFunctionSubring ℂ D → C(D, ℂ)) '' A)) := by
  letI : LocallyCompactSpace D := hD_open.locallyCompactSpace
  let hA' := holomorphic_derivative_image_uniformly_bounded_on_compacts hD_open hA
  let e : analyticFunctionSubring ℂ D → C(D, ℂ) := fun f ↦ (f : C(D, ℂ))
  let S : Set C(D, ℂ) := e '' A
  have hClosedEmbedding :
      Topology.IsClosedEmbedding
        (UniformOnFun.ofFun {K : Set D | IsCompact K} ∘
          (fun f : C(D, ℂ) ↦ (f : D → ℂ))) := by
    have hrange :
        Set.range
            (UniformOnFun.ofFun {K : Set D | IsCompact K} ∘
              (fun f : C(D, ℂ) ↦ (f : D → ℂ))) =
          {f : UniformOnFun D ℂ {K | IsCompact K} | Continuous f} := by
      simpa [Function.comp, ContinuousMap.toUniformOnFunIsCompact] using
        (ContinuousMap.range_toUniformOnFunIsCompact (α := D) (β := ℂ))
    have hClosedRange :
        IsClosed
          (Set.range
            (UniformOnFun.ofFun {K : Set D | IsCompact K} ∘
              (fun f : C(D, ℂ) ↦ (f : D → ℂ)))) := by
      rw [hrange]
      exact UniformOnFun.isClosed_setOf_continuous CompactlyCoherentSpace.isCoherentWith
    exact ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, hClosedRange⟩
  have hEquicont :
      Equicontinuous (fun u : S ↦ ((u : C(D, ℂ)) : D → ℂ)) := by
    intro x
    rcases (isCompact_singleton (x := (x : ℂ))).exists_cthickening_subset_open hD_open
        (by simp [x.2]) with ⟨δ, hδ, hδD⟩
    have hclosedBallD : Metric.closedBall (x : ℂ) (δ / 2) ⊆ D := by
      refine (Metric.closedBall_subset_cthickening (by simp : (x : ℂ) ∈ ({(x : ℂ)} : Set ℂ))
          (δ / 2)).trans ?_
      exact (Metric.cthickening_mono (by linarith) _).trans hδD
    obtain ⟨M, hM⟩ := hA' (K := Metric.closedBall (x : ℂ) (δ / 2))
      (isCompact_closedBall _ _) hclosedBallD
    let L : ℝ := max M 0
    have hL_nonneg : 0 ≤ L := le_max_right _ _
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    refine ⟨min (δ / 2) (ε / (L + 1)), by positivity, ?_⟩
    intro y hy u
    rcases u.2 with ⟨f, hf, hfu⟩
    have hu_eq : (u : C(D, ℂ)) = (f : C(D, ℂ)) := by
      simpa using hfu.symm
    rcases f.2 with ⟨F, hF, hF_eq⟩
    have hy_half : dist (x : ℂ) (y : ℂ) < δ / 2 := by
      simpa [dist_comm] using lt_of_lt_of_le hy (min_le_left _ _)
    let g : analyticFunctionSubring ℂ D :=
      ⟨D.restrict (deriv F), ⟨deriv F, hF.deriv_of_isOpen hD_open, rfl⟩⟩
    have hderiv_mem : g ∈ HolomorphicDerivativeImage D A := by
      exact ⟨f, hf, F, hF, hF_eq, rfl⟩
    have hsegment_closed :
        segment ℝ (x : ℂ) (y : ℂ) ⊆ Metric.closedBall (x : ℂ) (δ / 2) := by
      intro z hz
      have hzball : z ∈ Metric.closedBall (x : ℂ) (dist (x : ℂ) (y : ℂ)) :=
        (segment_subset_closedBall_left (x : ℂ) (y : ℂ)) hz
      exact le_trans (Metric.mem_closedBall.mp hzball) hy_half.le
    have hsegment_diff :
        ∀ z ∈ segment ℝ (x : ℂ) (y : ℂ), DifferentiableAt ℂ F z := by
      intro z hz
      exact DifferentiableOn.differentiableAt hF.differentiableOn
        (hD_open.mem_nhds (hclosedBallD (hsegment_closed hz)))
    have hsegment_bound :
        ∀ z ∈ segment ℝ (x : ℂ) (y : ℂ), ‖deriv F z‖ ≤ L := by
      intro z hz
      have hz_closed : z ∈ Metric.closedBall (x : ℂ) (δ / 2) := hsegment_closed hz
      have hzD : z ∈ D := hclosedBallD hz_closed
      have hzM :
          ‖g ⟨z, hzD⟩‖ ≤ M :=
        hM g hderiv_mem z hz_closed
      have hz_norm : ‖deriv F z‖ ≤ M := by
        simpa [g] using hzM
      exact le_trans hz_norm (le_max_left _ _)
    have hdist_le :
        dist ((f : C(D, ℂ)) x) ((f : C(D, ℂ)) y) ≤ L * dist x y := by
      have hx_eval : (f : C(D, ℂ)) x = F x := by
        simpa using (congrArg (fun g : D → ℂ ↦ g x) hF_eq).symm
      have hy_eval : (f : C(D, ℂ)) y = F y := by
        simpa using (congrArg (fun g : D → ℂ ↦ g y) hF_eq).symm
      have hnormF :
          ‖F y - F x‖ ≤ L * ‖(y : ℂ) - (x : ℂ)‖ := by
        simpa using
          (convex_segment (x : ℂ) (y : ℂ)).norm_image_sub_le_of_norm_deriv_le
            hsegment_diff hsegment_bound
            (left_mem_segment ℝ (x : ℂ) (y : ℂ))
            (right_mem_segment ℝ (x : ℂ) (y : ℂ))
      have hnorm_le :
          ‖(f : C(D, ℂ)) y - (f : C(D, ℂ)) x‖ ≤ L * ‖(y : ℂ) - (x : ℂ)‖ := by
        simpa [hx_eval, hy_eval] using hnormF
      have hxy_norm : ‖(y : ℂ) - (x : ℂ)‖ = dist x y := by
        change ‖(y : ℂ) - (x : ℂ)‖ = dist (x : ℂ) (y : ℂ)
        rw [dist_eq_norm]
        exact norm_sub_rev _ _
      rw [← hxy_norm]
      simpa [dist_eq_norm, norm_sub_rev] using hnorm_le
    have hLt :
        L * dist x y < ε := by
      have hy_eps : dist x y < ε / (L + 1) := by
        simpa [dist_comm] using lt_of_lt_of_le hy (min_le_right _ _)
      have hL1_pos : 0 < L + 1 := by linarith
      have hdist_nonneg : 0 ≤ dist x y := dist_nonneg
      have hmul_lt : (L + 1) * dist x y < ε := by
        have htmp : dist x y * (L + 1) < ε := (lt_div_iff₀ hL1_pos).mp hy_eps
        simpa [mul_comm] using htmp
      have hle : L * dist x y ≤ (L + 1) * dist x y := by
        nlinarith
      exact lt_of_le_of_lt hle hmul_lt
    simpa [hu_eq] using lt_of_le_of_lt hdist_le hLt
  have hPointwiseCompact :
      ∀ K ∈ ({K : Set D | IsCompact K} : Set (Set D)), ∀ x ∈ K,
        ∃ Q, IsCompact Q ∧ ∀ u ∈ S, ((u : C(D, ℂ)) x) ∈ Q := by
    intro K hK x hx
    obtain ⟨M, hM⟩ := hA (K := ({(x : ℂ)} : Set ℂ))
      (show IsCompact ({(x : ℂ)} : Set ℂ) from isCompact_singleton)
      (by
        intro z hz
        rcases Set.mem_singleton_iff.mp hz with rfl
        exact x.2)
    refine ⟨Metric.closedBall (0 : ℂ) M, isCompact_closedBall _ _, ?_⟩
    intro u hu
    rcases hu with ⟨f, hf, hfu⟩
    have hu_eq : (u : C(D, ℂ)) = (f : C(D, ℂ)) := by
      simpa using hfu.symm
    simpa [Metric.mem_closedBall, dist_eq_norm, hu_eq] using
      hM f hf x (by simp : (x : ℂ) ∈ ({(x : ℂ)} : Set ℂ))
  simpa [S, e] using
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖_compact := fun K hK ↦ hK)
      (F_clemb := hClosedEmbedding)
      (s := S)
      (s_eqcont := fun K hK ↦ hEquicont.equicontinuousOn K)
      (s_pointwiseCompact := hPointwiseCompact)

theorem normalized_disc_admissible_family_isCompact {Δ : Set ℂ}
    (hΔ_open : IsOpen Δ) (hΔ_simply : IsSimplyConnected Δ) (h0Δ : (0 : ℂ) ∈ Δ) :
    IsCompact (((↑) : analyticFunctionSubring ℂ Δ → C(Δ, ℂ)) ''
      normalized_disc_admissible_family Δ) := by
  -- Apply Cartan's bounded-plus-closed compactness theorem to the already packaged family `B`.
  refine holomorphic_compact_of_bounded_closed
    (hrelcompact := fun A hA ↦
      holomorphic_family_closure_isCompact_of_uniformlyBoundedOnCompacta hΔ_open hA)
    (hA_bounded := normalized_disc_admissible_family_uniformlyBoundedOnCompacta)
    (hA_closed := normalized_disc_admissible_family_isClosed hΔ_open hΔ_simply h0Δ)

/-- Helper for Theorem VI.3-extra-1: after compactness of the admissible family `B`, Cartan's
source proof only needs the derivative-maximizing extraction step. -/
theorem exists_admissible_map_with_maximal_deriv_norm {Δ : Set ℂ}
    (hΔ_open : IsOpen Δ) (hΔ_simply : IsSimplyConnected Δ) (h0Δ : (0 : ℂ) ∈ Δ)
    (hΔ_subset : Δ ⊆ Metric.ball (0 : ℂ) 1) :
    ∃ f : ℂ → ℂ, IsNormalizedUnivalentDiscMapOn Δ f ∧ 1 ≤ ‖deriv f 0‖ ∧
      ∀ g : ℂ → ℂ, IsNormalizedUnivalentDiscMapOn Δ g → ‖deriv g 0‖ ≤ ‖deriv f 0‖ := by
  classical
  letI : LocallyCompactSpace Δ := hΔ_open.locallyCompactSpace
  letI := continuousMap_metrizable_preconditions_of_isOpen (X := ℂ) (E := ℂ) Δ hΔ_open
  let AΔ := normalized_disc_admissible_family Δ
  have hA_nonempty : AΔ.Nonempty :=
    normalized_disc_admissible_family_nonempty hΔ_subset
  let K : Set C(Δ, ℂ) := (((↑) : analyticFunctionSubring ℂ Δ → C(Δ, ℂ)) '' AΔ)
  have hK_compact : IsCompact K :=
    normalized_disc_admissible_family_isCompact hΔ_open hΔ_simply h0Δ
  let chosenMember : K → analyticFunctionSubring ℂ Δ := fun u ↦ Classical.choose u.2
  have hchosen_mem : ∀ u : K, chosenMember u ∈ AΔ := by
    intro u
    exact (Classical.choose_spec u.2).1
  have hchosen_coe : ∀ u : K, ((chosenMember u : analyticFunctionSubring ℂ Δ) : C(Δ, ℂ)) = u.1 := by
    intro u
    exact (Classical.choose_spec u.2).2
  let chosenMap : K → ℂ → ℂ := fun u ↦ Classical.choose (hchosen_mem u)
  have hchosen_admissible : ∀ u : K, IsNormalizedUnivalentDiscMapOn Δ (chosenMap u) := by
    intro u
    exact (Classical.choose_spec (hchosen_mem u)).1
  have hchosen_deriv_ge : ∀ u : K, 1 ≤ ‖deriv (chosenMap u) 0‖ := by
    intro u
    exact (Classical.choose_spec (hchosen_mem u)).2.1
  have hchosen_restrict : ∀ u : K, Δ.restrict (chosenMap u) = chosenMember u := by
    intro u
    exact (Classical.choose_spec (hchosen_mem u)).2.2
  let derivNormOnK : K → ℝ := fun u ↦ ‖deriv (chosenMap u) 0‖
  have hderivNorm_eq :
      ∀ {u : analyticFunctionSubring ℂ Δ} (hu : u ∈ AΔ) {f : ℂ → ℂ},
        IsNormalizedUnivalentDiscMapOn Δ f →
        1 ≤ ‖deriv f 0‖ →
        Δ.restrict f = u →
        derivNormOnK ⟨(u : C(Δ, ℂ)), ⟨u, hu, rfl⟩⟩ = ‖deriv f 0‖ := by
    intro u hu f hf hf_deriv hf_restrict
    let x : K := ⟨(u : C(Δ, ℂ)), ⟨u, hu, rfl⟩⟩
    have hmember_eq : chosenMember x = u := by
      ext z
      have hz_eval := congrArg (fun g : C(Δ, ℂ) ↦ g z) (hchosen_coe x)
      simpa [x] using hz_eval
    have hmember_eq_fun : (chosenMember x : Δ → ℂ) = u := by
      simpa using congrArg (fun v : analyticFunctionSubring ℂ Δ ↦ (v : Δ → ℂ)) hmember_eq
    have hrestrict_eq : Δ.restrict (chosenMap x) = Δ.restrict f := by
      -- Both representatives define the same element of the admissible family image.
      calc
        Δ.restrict (chosenMap x) = chosenMember x := hchosen_restrict x
        _ = u := hmember_eq_fun
        _ = Δ.restrict f := hf_restrict.symm
    have hderiv_eq : deriv (chosenMap x) 0 = deriv f 0 :=
      deriv_eq_of_restrict_eq hΔ_open h0Δ hrestrict_eq
    simpa [derivNormOnK, x] using congrArg norm hderiv_eq
  have hderivNorm_cont : Continuous derivNormOnK := by
    rw [continuous_iff_seqContinuous]
    intro x y hxy
    let W : ℕ → analyticFunctionSubring ℂ Δ := fun n ↦ chosenMember (x n)
    let F : ℕ → ℂ → ℂ := fun n ↦ chosenMap (x n)
    let f : ℂ → ℂ := chosenMap y
    have hx_val :
        Tendsto (fun n ↦ (x n).1) atTop (𝓝 y.1) :=
      (continuous_subtype_val.tendsto y).comp hxy
    have hW_tendsto :
        Tendsto (fun n ↦ ((W n : analyticFunctionSubring ℂ Δ) : C(Δ, ℂ))) atTop (𝓝 y.1) := by
      -- Replace the chosen admissible representatives by the original convergent sequence in `K`.
      refine Tendsto.congr' ?_ hx_val
      exact Filter.Eventually.of_forall fun n ↦ (hchosen_coe (x n)).symm
    have hF_loc :
        TendstoLocallyUniformlyOn F f atTop Δ := by
      -- Compact-open convergence on `K` becomes locally uniform convergence on the domain `Δ`.
      rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
      have hloc_sub :
          TendstoLocallyUniformly (fun n (z : Δ) ↦ (W n : C(Δ, ℂ)) z) y.1 atTop :=
        (ContinuousMap.tendsto_iff_tendstoLocallyUniformly).1 hW_tendsto
      have hF_sub : TendstoLocallyUniformly (fun n (z : Δ) ↦ F n z) y.1 atTop := by
        exact hloc_sub.congr fun n z ↦ by
          have hz_eval := congrArg (fun h : Δ → ℂ ↦ h z) (hchosen_restrict (x n))
          simpa [F, W] using hz_eval.symm
      exact hF_sub.congr_right fun z ↦ by
        have hy_coe :=
          congrArg (fun h : C(Δ, ℂ) ↦ h z) (hchosen_coe y).symm
        have hy_restrict :=
          congrArg (fun h : Δ → ℂ ↦ h z) (hchosen_restrict y)
        calc
          y.1 z = ((chosenMember y : analyticFunctionSubring ℂ Δ) : C(Δ, ℂ)) z := by
            simpa using hy_coe
          _ = f z := by
            simpa [f] using hy_restrict.symm
    have hF_diff : ∀ n, DifferentiableOn ℂ (F n) Δ := by
      intro n
      exact (hchosen_admissible (x n)).differentiableOn
    have hderiv_tendsto :
        Tendsto (fun n ↦ deriv (F n) 0) atTop (𝓝 (deriv f 0)) := by
      -- Derivatives converge at the center because the admissible family stays holomorphic.
      exact (tendsto_locally_uniformly_on_compacts_deriv hΔ_open hF_diff hF_loc).tendsto_at h0Δ
    simpa [derivNormOnK, F, f] using
      (continuous_norm.tendsto _).comp hderiv_tendsto
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK_compact
  rcases hA_nonempty with ⟨u₀, hu₀⟩
  let x₀ : K := ⟨(u₀ : C(Δ, ℂ)), ⟨u₀, hu₀, rfl⟩⟩
  obtain ⟨uMax, -, huMax⟩ :=
    isCompact_univ.exists_isMaxOn (β := K) (α := ℝ) ⟨x₀, by simp⟩ hderivNorm_cont.continuousOn
  rw [isMaxOn_iff] at huMax
  let f : ℂ → ℂ := chosenMap uMax
  have hf : IsNormalizedUnivalentDiscMapOn Δ f := hchosen_admissible uMax
  have hf_deriv : 1 ≤ ‖deriv f 0‖ := hchosen_deriv_ge uMax
  refine ⟨f, hf, hf_deriv, ?_⟩
  intro g hg
  by_cases hg_deriv : 1 ≤ ‖deriv g 0‖
  · let ug : analyticFunctionSubring ℂ Δ :=
      ⟨Δ.restrict g, ⟨g, hg.analyticOnNhd, rfl⟩⟩
    have hug : ug ∈ AΔ := by
      -- In the source family `B`, the lower derivative bound is the only extra condition.
      exact ⟨g, hg, hg_deriv, rfl⟩
    let kg : K := ⟨(ug : C(Δ, ℂ)), ⟨ug, hug, rfl⟩⟩
    have hkg_value : derivNormOnK kg = ‖deriv g 0‖ := by
      exact hderivNorm_eq hug hg hg_deriv rfl
    have hmax_kg : derivNormOnK kg ≤ derivNormOnK uMax := huMax kg (by simp)
    have hmax_g : ‖deriv g 0‖ ≤ derivNormOnK uMax := by
      simpa [hkg_value] using hmax_kg
    simpa [derivNormOnK, f] using hmax_g
  · -- Outside `B`, the derivative norm is already below `1`, while the maximizer lies in `B`.
    exact le_trans (lt_of_not_ge hg_deriv).le hf_deriv

/-- Helper for Theorem VI.3-extra-1: on a simply connected domain inside the unit disc containing
`0`, the compactness argument should produce a normalized univalent map with maximal derivative at
`0`. -/
theorem exists_extremal_normalized_disc_map {Δ : Set ℂ}
    (hΔ_open : IsOpen Δ) (hΔ_simply : IsSimplyConnected Δ) (h0Δ : (0 : ℂ) ∈ Δ)
    (hΔ_subset : Δ ⊆ Metric.ball (0 : ℂ) 1) :
    ∃ f : ℂ → ℂ, IsNormalizedUnivalentDiscMapOn Δ f ∧
      ∀ g : ℂ → ℂ, IsNormalizedUnivalentDiscMapOn Δ g → ‖deriv g 0‖ ≤ ‖deriv f 0‖ := by
  rcases exists_admissible_map_with_maximal_deriv_norm hΔ_open hΔ_simply h0Δ hΔ_subset with
    ⟨f, hf, -, hmax⟩
  -- Forget the auxiliary lower bound `1 ≤ ‖deriv f 0‖`; only maximality is needed here.
  exact ⟨f, hf, hmax⟩

-- Domain sampling note:
-- * source-facing layer: the theorem asserts existence of a biholomorphic correspondence from `D`
--   to the open unit disc;
-- * core/canonical owner in this chapter: `HolomorphicIsomorph`;
-- * discarded bridge/view layer: the older section-24 raw tuple surface of forward map, inverse,
--   `MapsTo`, `DifferentiableOn`, and `LeftInvOn` data.

/-- Theorem VI.3-extra-1: any simply connected open subset `D` of the complex plane, different
from the whole plane, is biholomorphic to the open unit disc. -/
theorem simply_connected_open_set_biholomorphic_to_open_unit_disc {D : Set ℂ}
    (hD_open : IsOpen D) (hD_simplyConnected : IsSimplyConnected D) (hD_proper : D ≠ univ) :
    Nonempty (HolomorphicIsomorph D (Metric.ball (0 : ℂ) 1)) := by
  rcases exists_centered_subdisc_model hD_open hD_simplyConnected hD_proper with
    ⟨Δ, eΔ, hΔ_open, hΔ_simply, h0Δ, hΔ_subset⟩
  have hΔ_proper : Δ ≠ univ := by
    intro hΔ_univ
    apply unitDisc_ne_univ
    ext z
    constructor
    · intro hz
      simp
    · intro hz
      have hzΔ : z ∈ Δ := by simp [hΔ_univ]
      exact hΔ_subset hzΔ
  rcases exists_extremal_normalized_disc_map hΔ_open hΔ_simply h0Δ hΔ_subset with
    ⟨f, hf, hmax⟩
  have himage : f '' Δ = Metric.ball (0 : ℂ) 1 := by
    -- Proposition 3.1 upgrades maximality of the derivative norm to surjectivity onto the disc.
    exact (image_eq_unitDisc_iff_deriv_norm_maximal_at_zero
      hΔ_open hΔ_simply hΔ_proper h0Δ hf).2 hmax
  -- Package the extremal map into the chapter owner and compose back with the normalization model.
  exact ⟨eΔ.trans (hf.toHolomorphicIsomorph hΔ_open himage)⟩
