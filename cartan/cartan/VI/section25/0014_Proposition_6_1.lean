import Mathlib
import cartan.III.section11.«0009_Proposition_4_2»
import cartan.VI.section25.«0013_Definition_VI_4_extra_11»

universe uX uY

open Filter Set Complex
open scoped Manifold
open scoped Topology
local macro:max "MDiff" ppSpace t:term:arg : term =>
  `(MDifferentiable 𝓘(ℂ) 𝓘(ℂ) $t)

-- Domain sampling:
-- * primary domain: one-dimensional complex manifolds, ramification, and biholomorphic
--   equivalences;
-- * source-facing owner declarations in this chapter: `has_ramification_index_at` and
--   `unramified_at`;
-- * core/canonical mathlib owners: `IsLocalDiffeomorphAt`, `IsLocalDiffeomorph`, and
--   `IsLocalDiffeomorph.diffeomorphOfBijective`;
-- * bridge layer here: Proposition 6.1 should first expose that a simple holomorphic map is
--   unramified at each point, then package the equivalent local-biholomorphism and global
--   biholomorphism consequences through the mathlib owner API.
-- Primitive data here is only the holomorphic map together with injectivity; the local/global
-- diffeomorphism API and the resulting biholomorphic isomorphism are derived.

section

variable {X : Type uX} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
variable {Y : Type uY} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Helper for Proposition 6.1: the image of an open subset of the chart source by the preferred
extended chart is open in `ℂ`. -/
lemma isOpen_image_extChartAt_of_subset_source {s : Set X} {a : X} (hs_open : IsOpen s)
    (hs_subset : s ⊆ (extChartAt 𝓘(ℂ) a).source) : IsOpen ((extChartAt 𝓘(ℂ) a) '' s) := by
  have hs_chart : s ⊆ (chartAt ℂ a).source := by
    simpa [extChartAt_source (I := 𝓘(ℂ))] using hs_subset
  have hchart_open : IsOpen ((chartAt ℂ a) '' s) := by
    exact (chartAt ℂ a).isOpen_image_of_subset_source hs_open hs_chart
  simpa [extChartAt_coe, Function.comp, Set.image_image] using
    (𝓘(ℂ).toHomeomorph.isOpen_image).2 hchart_open

omit [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y] in
/-- Helper for Proposition 6.1: the preferred chart expression of an injective map remains
injective on the chart image of the common source neighborhood. -/
lemma written_in_extChartAt_injOn {f : X → Y}
    (hsimple : Function.Injective f) (a : X) :
    let S : Set X := (extChartAt 𝓘(ℂ) a).source ∩ f ⁻¹' (extChartAt 𝓘(ℂ) (f a)).source
    let U : Set ℂ := (extChartAt 𝓘(ℂ) a) '' S
    Set.InjOn (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f) U := by
  dsimp
  intro z hz z' hz' hzz'
  rcases hz with ⟨x, hxS, rfl⟩
  rcases hz' with ⟨x', hx'S, rfl⟩
  -- On the chosen chart image, the preferred coordinate expression is the honest chart formula.
  have hchart :
      (extChartAt 𝓘(ℂ) (f a)) (f ((extChartAt 𝓘(ℂ) a).symm ((extChartAt 𝓘(ℂ) a) x))) =
        (extChartAt 𝓘(ℂ) (f a)) (f ((extChartAt 𝓘(ℂ) a).symm ((extChartAt 𝓘(ℂ) a) x'))) := by
    simpa only [writtenInExtChartAt] using hzz'
  rw [(extChartAt 𝓘(ℂ) a).left_inv hxS.1, (extChartAt 𝓘(ℂ) a).left_inv hx'S.1] at hchart
  have hfx : f x = f x' :=
    (extChartAt 𝓘(ℂ) (f a)).injOn hxS.2 hx'S.2 hchart
  exact congrArg (extChartAt 𝓘(ℂ) a) (hsimple hfx)

/-- Helper for Proposition 6.1: the preferred chart expression of a holomorphic map is analytic on
the common chart neighborhood where both source and target charts are valid. -/
lemma written_in_extChartAt_analyticOnNhd_of_holomorphic {f : X → Y}
    (hf : MDiff f) (a : X) :
    let S : Set X := (extChartAt 𝓘(ℂ) a).source ∩ f ⁻¹' (extChartAt 𝓘(ℂ) (f a)).source
    let U : Set ℂ := (extChartAt 𝓘(ℂ) a) '' S
    AnalyticOnNhd ℂ (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f) U := by
  dsimp
  let S : Set X := (extChartAt 𝓘(ℂ) a).source ∩ f ⁻¹' (extChartAt 𝓘(ℂ) (f a)).source
  let U : Set ℂ := (extChartAt 𝓘(ℂ) a) '' S
  have hS_subset : S ⊆ (extChartAt 𝓘(ℂ) a).source := by
    intro x hx
    exact hx.1
  have hS_maps : MapsTo f S (extChartAt 𝓘(ℂ) (f a)).source := by
    intro x hx
    exact hx.2
  have hS_open : IsOpen S := by
    -- The common chart neighborhood is the intersection of two open chart-source conditions.
    exact
      (isOpen_extChartAt_source a).inter
        ((isOpen_extChartAt_source (f a)).preimage hf.continuous)
  have hU_open : IsOpen U := by
    -- The source chart is an open partial homeomorphism on its source.
    simpa [U] using isOpen_image_extChartAt_of_subset_source hS_open hS_subset
  have hmdiffS : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f S := by
    exact hf.mdifferentiableOn.mono fun _x hx ↦ hx
  have hdiffU :
      DifferentiableOn ℂ (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f) U := by
    -- On a single source/target chart pair, manifold differentiability is ordinary complex
    -- differentiability of the chart expression.
    simpa [S, U, writtenInExtChartAt] using
      (mdifferentiableOn_iff_of_subset_source' (I := 𝓘(ℂ)) (I' := 𝓘(ℂ))
        (f := f) (s := S) (x := a) (y := f a) hS_subset hS_maps).1 hmdiffS
  exact (Complex.analyticOnNhd_iff_differentiableOn hU_open).2 hdiffU

/-- Helper for Proposition 6.1: an injective analytic map on an open planar domain cannot be
eventually constant at a point of the domain. -/
lemma injective_analyticOnNhd_not_eventually_const_at {U : Set ℂ} {g : ℂ → ℂ}
    (hU_open : IsOpen U) (hinj : Set.InjOn g U) {z : ℂ} (hz : z ∈ U) :
    ¬ ∀ᶠ w in 𝓝 z, g w = g z := by
  intro hconst
  have hconst_ne : ∀ᶠ w in 𝓝[≠] z, g w = g z :=
    hconst.filter_mono nhdsWithin_le_nhds
  -- A punctured neighborhood point of `U` with the same image contradicts injectivity.
  have hwitness : {w : ℂ | w ≠ z ∧ w ∈ U ∧ g w = g z} ∈ 𝓝[≠] z := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hU_open.mem_nhds hz),
      hconst_ne] with w hw_ne hwU hwg
    exact ⟨hw_ne, hwU, hwg⟩
  rcases Filter.nonempty_of_mem hwitness with ⟨w, hw_ne, hwU, hwg⟩
  exact hw_ne (hinj hwU hz hwg)

/-- Helper for Proposition 6.1: if the derivative vanishes at `z`, then the shifted function
`w ↦ g w - g z` has analytic order at least `2` at `z`. -/
lemma analyticOrderAt_sub_two_le_of_deriv_zero {U : Set ℂ} {g : ℂ → ℂ}
    (hanalytic : AnalyticOnNhd ℂ g U) {z : ℂ} (hz : z ∈ U) (hderiv : deriv g z = 0) :
    (2 : ℕ∞) ≤ analyticOrderAt (fun w ↦ g w - g z) z := by
  have hz_analytic : AnalyticAt ℂ (fun w ↦ g w - g z) z := (hanalytic z hz).sub analyticAt_const
  -- The shifted function and its first derivative vanish at the base point.
  change (2 : ℕ) ≤ analyticOrderAt (fun w ↦ g w - g z) z
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hz_analytic]
  intro i hi
  have hi' : i = 0 ∨ i = 1 := by omega
  cases hi' with
  | inl h0 =>
      simp [h0, iteratedDeriv_zero]
  | inr h1 =>
      simp [h1, iteratedDeriv_one, hderiv]

/-- Helper for Proposition 6.1: an injective analytic map on an open subset of `ℂ` has
nonvanishing derivative at each point of that subset. -/
lemma injective_analyticOnNhd_deriv_ne_zero {U : Set ℂ} {g : ℂ → ℂ}
    (hU_open : IsOpen U) (hanalytic : AnalyticOnNhd ℂ g U) (hinj : Set.InjOn g U)
    {z : ℂ} (hz : z ∈ U) :
    deriv g z ≠ 0 := by
  intro hderiv
  -- Route correction: use the section22 multiplicity-count contradiction instead of extracting
  -- explicit distinct preimages from the nearby fiber theorem.
  have htwo :
      (2 : ℕ∞) ≤ analyticOrderAt (fun w ↦ g w - g z) z :=
    analyticOrderAt_sub_two_le_of_deriv_zero hanalytic hz hderiv
  have hnot_top : analyticOrderAt (fun w ↦ g w - g z) z ≠ ⊤ := by
    intro htop
    obtain ⟨c, hc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.mp <|
      (eventuallyConst_iff_analyticOrderAt_sub_eq_top).2 htop
    have hcz : c = g z := by
      simpa using (hc.self_of_nhds).symm
    exact injective_analyticOnNhd_not_eventually_const_at hU_open hinj hz <|
      by simpa [hcz] using hc
  let k : ℕ := analyticOrderNatAt (fun w ↦ g w - g z) z
  have hk : analyticOrderAt (fun w ↦ g w - g z) z = k := by
    rw [← Nat.cast_analyticOrderNatAt hnot_top]
  have hk_two : 2 ≤ k := by
    have htwo' : (2 : ℕ∞) ≤ (k : ℕ∞) := by simpa [hk] using htwo
    exact_mod_cast htwo'
  have hk_pos : 0 < k := by omega
  -- Shrink to a ball inside `U`, then compare the multiplicity theorem with injectivity.
  obtain ⟨rU, hrU_pos, hrU_subset⟩ := Metric.mem_nhds_iff.mp (hU_open.mem_nhds hz)
  obtain ⟨r₀, hr₀_pos, hr₀⟩ :=
    nearby_level_set_has_k_simple_roots (f := g) (z₀ := z) (a := g z) (k := k) hk_pos hk
  let r : ℝ := min rU r₀
  have hr_pos : 0 < r := by
    exact lt_min hrU_pos hr₀_pos
  have hr_le : r ≤ r₀ := min_le_right _ _
  have hr_subset : Metric.ball z r ⊆ U := by
    intro w hw
    have hwU : w ∈ Metric.ball z rU := by
      simpa [Metric.mem_ball, r] using (lt_of_lt_of_le hw (min_le_left rU r₀))
    exact hrU_subset hwU
  obtain ⟨δ, hδ_pos, hδ⟩ := hr₀ r hr_pos hr_le
  let b : ℂ := g z + (((δ / 2 : ℝ) : ℂ))
  have hb_sub : b - g z = (((δ / 2 : ℝ) : ℂ)) := by
    simp [b]
  have hb_dist : ‖b - g z‖ < δ := by
    calc
      ‖b - g z‖ = ‖δ / 2‖ := by rw [hb_sub, Complex.norm_real]
      _ = |δ / 2| := Real.norm_eq_abs _
      _ = δ / 2 := by rw [abs_of_pos (half_pos hδ_pos)]
      _ < δ := by linarith
  have hhalf_ne : (((δ / 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (half_pos hδ_pos))
  have hb_ne : b ≠ g z := by
    intro hb_eq
    have hzero : b - g z = 0 := sub_eq_zero.mpr hb_eq
    have hhalf_zero : (((δ / 2 : ℝ) : ℂ)) = 0 := by simpa [hb_sub] using hzero
    exact hhalf_ne hhalf_zero
  obtain ⟨hfiber, -⟩ := hδ b hb_dist hb_ne
  have hfiber_le_one :
      {w : ℂ | w ∈ Metric.ball z r ∧ g w = b}.encard ≤ 1 := by
    refine (Set.encard_le_one_iff_subsingleton.2 ?_)
    intro w₁ hw₁ w₂ hw₂
    apply hinj
    · exact hr_subset hw₁.1
    · exact hr_subset hw₂.1
    · exact hw₁.2.trans hw₂.2.symm
  have hk_le_one_enat : (k : ℕ∞) ≤ 1 := by
    rw [← hfiber]
    exact hfiber_le_one
  have hk_le_one : k ≤ 1 := by
    exact_mod_cast hk_le_one_enat
  omega

/-- Helper for Proposition 6.1: injectivity forces the derivative of the centered preferred chart
expression to be nonzero at the chart-center. -/
lemma centered_chart_expression_deriv_ne_zero_of_simple {f : X → Y}
    (hf : MDiff f) (hsimple : Function.Injective f) (a : X) :
    deriv (centered_chart_expression_at f a) ((extChartAt 𝓘(ℂ) a) a) ≠ 0 := by
  let S : Set X := (extChartAt 𝓘(ℂ) a).source ∩ f ⁻¹' (extChartAt 𝓘(ℂ) (f a)).source
  let U : Set ℂ := (extChartAt 𝓘(ℂ) a) '' S
  have hU_open : IsOpen U := by
    -- The common chart image is open because the source chart is a local homeomorphism.
    have hS_open : IsOpen S := by
      exact
        (isOpen_extChartAt_source a).inter
          ((isOpen_extChartAt_source (f a)).preimage hf.continuous)
    have hS_subset : S ⊆ (extChartAt 𝓘(ℂ) a).source := by
      intro x hx
      exact hx.1
    simpa [U] using isOpen_image_extChartAt_of_subset_source hS_open hS_subset
  have hcenter_mem : (extChartAt 𝓘(ℂ) a) a ∈ U := by
    have hfa_source : f a ∈ (extChartAt 𝓘(ℂ) (f a)).source := by
      simp
    refine ⟨a, ⟨mem_extChartAt_source a, hfa_source⟩, rfl⟩
  have hderiv_written :
      deriv (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f) ((extChartAt 𝓘(ℂ) a) a) ≠ 0 := by
    -- Route correction: reduce the manifold statement to the planar injective-analytic core on
    -- the preferred chart domain.
    exact injective_analyticOnNhd_deriv_ne_zero
      hU_open
      (written_in_extChartAt_analyticOnNhd_of_holomorphic hf a)
      (written_in_extChartAt_injOn hsimple a) hcenter_mem
  -- Translating the target chart by a constant does not change the derivative.
  have hderiv_eq :
      deriv (centered_chart_expression_at f a) ((extChartAt 𝓘(ℂ) a) a) =
        deriv (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f) ((extChartAt 𝓘(ℂ) a) a) := by
    change
      deriv
          (fun z ↦
            writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f z - (extChartAt 𝓘(ℂ) (f a)) (f a))
          ((extChartAt 𝓘(ℂ) a) a) =
        deriv (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f) ((extChartAt 𝓘(ℂ) a) a)
    change
      deriv
          (fun z ↦
            (chartAt ℂ (f a)) (f ((chartAt ℂ a).symm z)) - (chartAt ℂ (f a)) (f a))
          ((chartAt ℂ a) a) =
        deriv (fun z ↦ (chartAt ℂ (f a)) (f ((chartAt ℂ a).symm z))) ((chartAt ℂ a) a)
    simp [deriv_sub_const]
  rw [hderiv_eq]
  exact hderiv_written

/-- Helper for Proposition 6.1: the uncentered preferred chart expression also has nonvanishing
derivative at the chart-center. -/
lemma written_in_extChartAt_deriv_ne_zero_of_simple {f : X → Y}
    (hf : MDiff f) (hsimple : Function.Injective f) (a : X) :
    deriv (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f) ((extChartAt 𝓘(ℂ) a) a) ≠ 0 := by
  have hderiv_eq :
      deriv (centered_chart_expression_at f a) ((extChartAt 𝓘(ℂ) a) a) =
        deriv (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f) ((extChartAt 𝓘(ℂ) a) a) := by
    change
      deriv
          (fun z ↦
            writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f z - (extChartAt 𝓘(ℂ) (f a)) (f a))
          ((extChartAt 𝓘(ℂ) a) a) =
        deriv (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f) ((extChartAt 𝓘(ℂ) a) a)
    change
      deriv
          (fun z ↦
            (chartAt ℂ (f a)) (f ((chartAt ℂ a).symm z)) - (chartAt ℂ (f a)) (f a))
          ((chartAt ℂ a) a) =
        deriv (fun z ↦ (chartAt ℂ (f a)) (f ((chartAt ℂ a).symm z))) ((chartAt ℂ a) a)
    simp [deriv_sub_const]
  rw [← hderiv_eq]
  exact centered_chart_expression_deriv_ne_zero_of_simple hf hsimple a

/-- Helper for Proposition 6.1: the centered preferred chart expression of a holomorphic map is
analytic at the chart-center. -/
lemma centered_chart_expression_analyticAt_of_holomorphic {f : X → Y}
    (hf : MDiff f) (a : X) :
    AnalyticAt ℂ (centered_chart_expression_at f a) ((extChartAt 𝓘(ℂ) a) a) := by
  let S : Set X := (extChartAt 𝓘(ℂ) a).source ∩ f ⁻¹' (extChartAt 𝓘(ℂ) (f a)).source
  let U : Set ℂ := (extChartAt 𝓘(ℂ) a) '' S
  have hcenter_mem : (extChartAt 𝓘(ℂ) a) a ∈ U := by
    have hfa_source : f a ∈ (extChartAt 𝓘(ℂ) (f a)).source := by
      simp
    refine ⟨a, ⟨mem_extChartAt_source a, hfa_source⟩, rfl⟩
  have hanalytic_written :
      AnalyticAt ℂ (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f) ((extChartAt 𝓘(ℂ) a) a) := by
    -- Evaluate the chart-domain analyticity lemma at the chart-center.
    exact (written_in_extChartAt_analyticOnNhd_of_holomorphic hf a) _ hcenter_mem
  -- The centered expression differs from the written chart expression by a constant translation.
  simpa [centered_chart_expression_at] using hanalytic_written.sub analyticAt_const

/-- Proposition 6.1, source-facing form: a simple holomorphic map between one-dimensional complex
manifolds is unramified at every point. -/
theorem simple_holomorphic_map_unramified_at {f : X → Y}
    (hf : MDiff f) (hsimple : Function.Injective f) (a : X) :
    unramified_at f a := by
  have hanalytic := centered_chart_expression_analyticAt_of_holomorphic hf a
  refine ⟨centered_chart_expression_analyticAt_of_holomorphic hf a, ?_⟩
  -- The chart-center is a simple zero because the centered expression vanishes there and has
  -- nonzero derivative.
  exact hanalytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (centered_chart_expression_at_self f a)
    (centered_chart_expression_deriv_ne_zero_of_simple hf hsimple a)

-- Proposition 6.1 now passes from the ramification calculation to the local inverse branch.
/-- Helper for Proposition 6.1: the chart expression has an invertible Fréchet derivative at the
chart-center, so the planar inverse function theorem applies there. -/
lemma written_in_extChartAt_hasFDerivAt_equiv_at_center {f : X → Y}
    (hf : MDiff f) (hsimple : Function.Injective f) (a : X) :
    let g := writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f
    let z0 := (extChartAt 𝓘(ℂ) a) a
    HasFDerivAt g
      (ContinuousLinearEquiv.unitsEquivAut ℂ
        (Units.mk0
          (deriv g z0)
          (written_in_extChartAt_deriv_ne_zero_of_simple hf hsimple a)) :
        ℂ →L[ℂ] ℂ)
      z0 := by
  dsimp
  let S : Set X := (extChartAt 𝓘(ℂ) a).source ∩ f ⁻¹' (extChartAt 𝓘(ℂ) (f a)).source
  let U : Set ℂ := (extChartAt 𝓘(ℂ) a) '' S
  have hz0_mem : (extChartAt 𝓘(ℂ) a) a ∈ U := by
    have hfa_source : f a ∈ (extChartAt 𝓘(ℂ) (f a)).source := by
      simp
    refine ⟨a, ⟨mem_extChartAt_source a, hfa_source⟩, rfl⟩
  have hanalytic :
      AnalyticAt ℂ (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f) ((extChartAt 𝓘(ℂ) a) a) :=
    (written_in_extChartAt_analyticOnNhd_of_holomorphic hf a) _ hz0_mem
  have hcont : ContDiffAt ℂ 1 (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f) ((extChartAt 𝓘(ℂ) a) a) :=
    hanalytic.contDiffAt
  have hderiv :
      deriv (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f) ((extChartAt 𝓘(ℂ) a) a) ≠ 0 :=
    written_in_extChartAt_deriv_ne_zero_of_simple hf hsimple a
  have hderivAt :
      HasDerivAt (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f)
        (deriv (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f) ((extChartAt 𝓘(ℂ) a) a))
        ((extChartAt 𝓘(ℂ) a) a) := by
    exact (hcont.differentiableAt one_ne_zero).hasDerivAt
  -- The scalar derivative is nonzero, hence it defines an invertible linear map of `ℂ`.
  exact hderivAt.hasFDerivAt_equiv hderiv

/-- Helper for Proposition 6.1: in preferred coordinates around `a`, the inverse function theorem
produces a local inverse branch on the natural chart domain. -/
lemma written_in_extChartAt_local_inverse_branch {f : X → Y}
    (hf : MDiff f) (hsimple : Function.Injective f) (a : X) :
    let g := writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f
    let z0 := (extChartAt 𝓘(ℂ) a) a
    let S : Set X := (extChartAt 𝓘(ℂ) a).source ∩ f ⁻¹' (extChartAt 𝓘(ℂ) (f a)).source
    let U : Set ℂ := (extChartAt 𝓘(ℂ) a) '' S
    ∃ δ : OpenPartialHomeomorph ℂ ℂ,
      z0 ∈ δ.source ∧
        δ.source ⊆ U ∧
          EqOn g δ δ.source ∧
            ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 δ δ.source ∧
              ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 δ.symm δ.target := by
  dsimp
  let g := writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f
  let z0 : ℂ := (extChartAt 𝓘(ℂ) a) a
  let S : Set X := (extChartAt 𝓘(ℂ) a).source ∩ f ⁻¹' (extChartAt 𝓘(ℂ) (f a)).source
  let U : Set ℂ := (extChartAt 𝓘(ℂ) a) '' S
  have hS_open : IsOpen S := by
    -- The common chart neighborhood is open on the source manifold.
    exact
      (isOpen_extChartAt_source a).inter
        ((isOpen_extChartAt_source (f a)).preimage hf.continuous)
  have hS_subset : S ⊆ (extChartAt 𝓘(ℂ) a).source := by
    intro x hx
    exact hx.1
  have hU_open : IsOpen U := by
    -- Its image under the source chart is therefore an open planar neighborhood.
    simpa [U] using isOpen_image_extChartAt_of_subset_source hS_open hS_subset
  have hz0_mem : z0 ∈ U := by
    have hfa_source : f a ∈ (extChartAt 𝓘(ℂ) (f a)).source := by
      simp
    refine ⟨a, ⟨mem_extChartAt_source a, hfa_source⟩, rfl⟩
  have hgCont : ContDiffAt ℂ 1 g z0 := by
    -- Analyticity of the chart expression gives the `C¹` input required by the inverse theorem.
    exact ((written_in_extChartAt_analyticOnNhd_of_holomorphic hf a) _ hz0_mem).contDiffAt
  have hgFDeriv : HasFDerivAt g
      (ContinuousLinearEquiv.unitsEquivAut ℂ
        (Units.mk0
          (deriv g z0)
          (written_in_extChartAt_deriv_ne_zero_of_simple hf hsimple a)) :
        ℂ →L[ℂ] ℂ)
      z0 :=
    written_in_extChartAt_hasFDerivAt_equiv_at_center hf hsimple a
  let δ₀ : OpenPartialHomeomorph ℂ ℂ := hgCont.toOpenPartialHomeomorph g hgFDeriv one_ne_zero
  let δ₁ : OpenPartialHomeomorph ℂ ℂ := δ₀.restrContDiff ℂ 1 (by norm_num)
  let δ : OpenPartialHomeomorph ℂ ℂ := δ₁.restrOpen U hU_open
  have hδ₀_source : z0 ∈ δ₀.source := by
    -- The inverse theorem keeps the base point in the source neighborhood.
    exact hgCont.mem_toOpenPartialHomeomorph_source hgFDeriv one_ne_zero
  have hδ₀_symm : ContDiffAt ℂ 1 δ₀.symm (g z0) := by
    -- The local inverse branch is also `C¹` at the image of the base point.
    simpa [δ₀, g] using hgCont.to_localInverse hgFDeriv one_ne_zero
  have hδ₁_source : z0 ∈ δ₁.source := by
    -- Restrict to the `C¹` locus without losing the base point.
    simpa [δ₁] using And.intro hδ₀_source (And.intro hgCont hδ₀_symm)
  have hsource_subset : δ.source ⊆ U := by
    intro z hz
    have hz' : z ∈ δ₁.source ∩ U := by
      simpa [δ] using hz
    exact hz'.2
  have hsource_subset_δ₁ : δ.source ⊆ δ₁.source := by
    intro z hz
    have hz' : z ∈ δ₁.source ∩ U := by
      simpa [δ] using hz
    exact hz'.1
  have htarget_subset_δ₁ : δ.target ⊆ δ₁.target := by
    intro w hw
    have hw' : w ∈ δ₁.target ∩ δ₁.symm ⁻¹' U := by
      simpa [δ] using hw
    exact hw'.1
  have hδ_smooth : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 δ δ.source := by
    have hδ_contDiff : ContDiffOn ℂ 1 δ δ.source := by
      simpa [δ, δ₁, δ₀] using
        (OpenPartialHomeomorph.contDiffOn_restrContDiff_source (𝕜 := ℂ) (f := δ₀) (n := 1)
          (by norm_num)).mono hsource_subset_δ₁
    simpa [contMDiffOn_iff_contDiffOn] using hδ_contDiff
  have hδ_symm_smooth : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 δ.symm δ.target := by
    have hδ_symm_contDiff : ContDiffOn ℂ 1 δ.symm δ.target := by
      simpa [δ, δ₁, δ₀] using
        (OpenPartialHomeomorph.contDiffOn_restrContDiff_target (𝕜 := ℂ) (f := δ₀) (n := 1)
          (by norm_num)).mono htarget_subset_δ₁
    simpa [contMDiffOn_iff_contDiffOn] using hδ_symm_contDiff
  refine ⟨δ, ?_, hsource_subset, ?_, hδ_smooth, hδ_symm_smooth⟩
  · -- After the final restriction to `U`, the chart-center still lies in the source.
    simpa [δ] using And.intro hδ₁_source hz0_mem
  · -- Route correction: both restrictions preserve the forward function, so the inverse-branch
    -- map still agrees pointwise with the chart expression on its source.
    intro z hz
    simp [δ, δ₁, δ₀, g]

/-- Helper for Proposition 6.1: transporting the planar inverse branch through the source and
target charts gives the manifold `PartialDiffeomorph` witnessing local biholomorphy. -/
lemma transport_local_inverse_branch_to_partial_diffeomorph {f : X → Y}
    (a : X)
    {δ : OpenPartialHomeomorph ℂ ℂ}
    (hz0 : (extChartAt 𝓘(ℂ) a) a ∈ δ.source)
    (hsource_subset :
      δ.source ⊆ (extChartAt 𝓘(ℂ) a) ''
        ((extChartAt 𝓘(ℂ) a).source ∩ f ⁻¹' (extChartAt 𝓘(ℂ) (f a)).source))
    (hEq :
      EqOn (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f) δ δ.source)
    (hδ_smooth : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 δ δ.source)
    (hδ_symm_smooth : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 δ.symm δ.target) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) X Y 1,
      a ∈ Φ.source ∧ EqOn f Φ Φ.source := by
  let e : OpenPartialHomeomorph X Y :=
    chartAt ℂ a ≫ₕ δ ≫ₕ (chartAt ℂ (f a)).symm
  have hchart : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (chartAt ℂ a) (chartAt ℂ a).source := by
    simpa [extChartAt_coe, Function.comp] using contMDiffOn_extChartAt (I := 𝓘(ℂ)) (x := a)
  have hchart_symm_a :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (chartAt ℂ a).symm (chartAt ℂ a).target := by
    simpa [extChartAt_coe_symm, Function.comp] using
      contMDiffOn_extChartAt_symm (I := 𝓘(ℂ)) (x := a)
  have hchart_fa : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (chartAt ℂ (f a)) (chartAt ℂ (f a)).source := by
    simpa [extChartAt_coe, Function.comp] using
      contMDiffOn_extChartAt (I := 𝓘(ℂ)) (x := f a)
  have hchart_symm :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (chartAt ℂ (f a)).symm (chartAt ℂ (f a)).target := by
    simpa [extChartAt_coe_symm, Function.comp] using
      contMDiffOn_extChartAt_symm (I := 𝓘(ℂ)) (x := f a)
  let Φ : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) X Y 1 :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := by
        -- Compose the source chart, the planar inverse branch, and the target chart inverse.
        simpa [e, OpenPartialHomeomorph.trans_apply, Function.comp_def,
          OpenPartialHomeomorph.trans_source, preimage_inter, inter_assoc,
          inter_left_comm, inter_comm] using
          hchart_symm.comp' (hδ_smooth.comp' hchart)
      contMDiffOn_invFun := by
        -- The inverse transport is the analogous composition in the reverse order.
        simpa [e, OpenPartialHomeomorph.trans_apply, Function.comp_def,
          OpenPartialHomeomorph.trans_target, preimage_inter, inter_assoc,
          inter_left_comm, inter_comm] using
          hchart_symm_a.comp' (hδ_symm_smooth.comp' hchart_fa) }
  have ha_source : a ∈ Φ.source := by
    -- The base point lies in the source chart and its chart coordinate lies in the planar branch.
    have htarget_mem :
        δ ((chartAt ℂ a) a) ∈ (chartAt ℂ (f a)).target := by
      have hsource_image :
          δ ((chartAt ℂ a) a) =
            writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f ((extChartAt 𝓘(ℂ) a) a) := by
        simpa [extChartAt_coe, Function.comp] using (hEq hz0).symm
      have hfa_source : f a ∈ (chartAt ℂ (f a)).source := by
        simp
      have htarget_eq : δ ((chartAt ℂ a) a) = (chartAt ℂ (f a)) (f a) := by
        calc
          δ ((chartAt ℂ a) a)
              = writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f ((extChartAt 𝓘(ℂ) a) a) := hsource_image
          _ = (chartAt ℂ (f a)) (f a) := by
                simp [writtenInExtChartAt, Function.comp]
      rw [htarget_eq]
      exact (chartAt ℂ (f a)).map_source hfa_source
    have hz_trans :
        (chartAt ℂ a) a ∈ (δ ≫ₕ (chartAt ℂ (f a)).symm).source := by
      rw [OpenPartialHomeomorph.trans_source]
      refine ⟨?_, htarget_mem⟩
      simpa [extChartAt_coe, Function.comp] using hz0
    change a ∈ (chartAt ℂ a).source ∩ ↑(chartAt ℂ a) ⁻¹' (δ ≫ₕ (chartAt ℂ (f a)).symm).source
    exact ⟨by simp, hz_trans⟩
  refine ⟨Φ, ha_source, ?_⟩
  intro x hx
  have hx' : x ∈ e.source := hx
  have hx_decomp :
      x ∈ (chartAt ℂ a).source ∩ (chartAt ℂ a ⁻¹' (δ ≫ₕ (chartAt ℂ (f a)).symm).source) := by
    simpa [e, OpenPartialHomeomorph.trans_source] using hx'
  have hx_chart : x ∈ (extChartAt 𝓘(ℂ) a).source := by
    simpa [extChartAt_source (I := 𝓘(ℂ))] using hx_decomp.1
  have hz_trans :
      (chartAt ℂ a) x ∈ (δ ≫ₕ (chartAt ℂ (f a)).symm).source := by
    exact hx_decomp.2
  have hz : (extChartAt 𝓘(ℂ) a) x ∈ δ.source := by
    rw [OpenPartialHomeomorph.trans_source] at hz_trans
    simpa [extChartAt_coe, Function.comp] using hz_trans.1
  have hzU :
      (extChartAt 𝓘(ℂ) a) x ∈
        (extChartAt 𝓘(ℂ) a) '' ((extChartAt 𝓘(ℂ) a).source ∩
          f ⁻¹' (extChartAt 𝓘(ℂ) (f a)).source) :=
    hsource_subset hz
  rcases hzU with ⟨x', hx'S, hx'chart⟩
  have hxx' : x = x' := by
    calc
      x = (chartAt ℂ a).symm ((chartAt ℂ a) x) := by
            rw [(chartAt ℂ a).left_inv (by simpa [extChartAt_source (I := 𝓘(ℂ))] using hx_chart)]
      _ = (chartAt ℂ a).symm ((chartAt ℂ a) x') := by
            simpa [extChartAt_coe, Function.comp] using
              (congrArg (chartAt ℂ a).symm hx'chart).symm
      _ = x' := by
            rw [(chartAt ℂ a).left_inv (by simpa [extChartAt_source (I := 𝓘(ℂ))] using hx'S.1)]
  subst x
  have htarget_source : f x' ∈ (extChartAt 𝓘(ℂ) (f a)).source := hx'S.2
  have hsource_chart : f x' ∈ (chartAt ℂ (f a)).source := by
    simpa [extChartAt_source (I := 𝓘(ℂ))] using htarget_source
  -- Unfold the transported map only at the current point and rewrite the planar branch by `hEq`.
  symm
  calc
    Φ x' = (chartAt ℂ (f a)).symm (δ ((extChartAt 𝓘(ℂ) a) x')) := by
      simp [Φ, e]
    _ = (chartAt ℂ (f a)).symm
          (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) a f ((extChartAt 𝓘(ℂ) a) x')) := by
            rw [hEq hz]
    _ = (chartAt ℂ (f a)).symm ((chartAt ℂ (f a)) (f ((chartAt ℂ a).symm ((chartAt ℂ a) x')))) := by
          simp [writtenInExtChartAt, Function.comp]
    _ = (chartAt ℂ (f a)).symm ((chartAt ℂ (f a)) (f x')) := by
          rw [(chartAt ℂ a).left_inv (by simpa [extChartAt_source (I := 𝓘(ℂ))] using hx'S.1)]
    _ = f x' := by
          exact (chartAt ℂ (f a)).left_inv hsource_chart

theorem simple_holomorphic_map_isLocalDiffeomorphAt {f : X → Y}
    (hf : MDiff f) (hsimple : Function.Injective f) (a : X) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) 1 f a := by
  -- Route correction: first build Cartan's inverse branch in planar coordinates, then transport it
  -- through the preferred charts to obtain the manifold local diffeomorphism witness.
  rcases written_in_extChartAt_local_inverse_branch hf hsimple a with
    ⟨δ, hz0, hsource_subset, hEq, hδ_smooth, hδ_symm_smooth⟩
  rcases transport_local_inverse_branch_to_partial_diffeomorph
      a hz0 hsource_subset hEq hδ_smooth hδ_symm_smooth with
    ⟨Φ, ha, hΦ⟩
  exact ⟨Φ, ha, hΦ⟩

/-- Proposition 6.1, global core/canonical bridge: a simple holomorphic map between
one-dimensional complex manifolds is locally biholomorphic. -/
theorem simple_holomorphic_map_isLocalDiffeomorph {f : X → Y}
    (hf : MDiff f) (hsimple : Function.Injective f) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 1 f :=
  fun a ↦ simple_holomorphic_map_isLocalDiffeomorphAt hf hsimple a

end
