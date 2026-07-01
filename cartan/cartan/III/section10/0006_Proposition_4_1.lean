import Mathlib
import cartan.III.section10.«0007_Definition_III_4_extra_5»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Function

open scoped Topology

/-- Proposition 4.1, owner form: if `0` is an isolated singularity of `f`, then that singularity
is removable if and only if `‖f‖` is bounded above along the punctured neighborhood filter at `0`.
Here removability is expressed by existence of an analytic extension agreeing with `f` on the
punctured neighborhood of `0`. -/
-- Proof sketch: for the forward implication, an analytic extension is continuous at `0`, hence
-- bounded on a sufficiently small neighbourhood, and therefore its restriction to the punctured
-- neighbourhood is bounded. For the reverse implication, expand `f` in a Laurent series on a
-- punctured disc and use Cauchy's inequalities to show that all negative coefficients vanish, so
-- the Laurent expansion reduces to a Taylor series defining the extension at `0`; the proof below
-- uses mathlib's canonical removable-singularity bridge `update f 0 (limUnder (𝓝[≠] 0) f)`.
theorem exists_analytic_extension_at_zero_iff_isBoundedUnder_norm
    {f : ℂ → ℂ} (hf : HasIsolatedSingularityAt f (0 : ℂ)) :
    (∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ f =ᶠ[𝓝[≠] (0 : ℂ)] g) ↔
      IsBoundedUnder (· ≤ ·) (𝓝[≠] (0 : ℂ)) (fun z ↦ ‖f z‖) := by
  constructor
  · rintro ⟨g, hg, hfg⟩
    have hg_bounded : IsBoundedUnder (· ≤ ·) (𝓝[≠] (0 : ℂ)) (fun z ↦ ‖g z‖) := by
      have hcont : ContinuousAt g 0 := hg.continuousAt
      have hnorm : ContinuousWithinAt (fun z ↦ ‖g z‖) ({(0 : ℂ)}ᶜ) 0 :=
        hcont.norm.continuousWithinAt
      have htendsto_norm : Tendsto (fun z ↦ ‖g z‖) (𝓝[≠] (0 : ℂ)) (𝓝 ‖g 0‖) := hnorm
      simpa using Tendsto.isBoundedUnder_le htendsto_norm
    have hnorm_eq : (fun z ↦ ‖f z‖) =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦ ‖g z‖ :=
      hfg.mono fun z hz ↦ by simp [hz]
    exact hg_bounded.mono_le hnorm_eq.le
  · intro hb
    have hdiff : ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ f z :=
      hf.eventually_analyticAt.mono fun z hz ↦ hz.differentiableAt
    obtain ⟨M, hM⟩ := hb.eventually_le
    have hb_sub : IsBoundedUnder (· ≤ ·) (𝓝[≠] (0 : ℂ)) (fun z ↦ ‖f z - f 0‖) := by
      have hbound : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖f z - f 0‖ ≤ M + ‖f 0‖ := by
        filter_upwards [hM] with z hz
        exact norm_sub_le_of_le hz le_rfl
      exact isBoundedUnder_of_eventually_le hbound
    let g : ℂ → ℂ := update f 0 (limUnder (𝓝[≠] (0 : ℂ)) f)
    have htendsto : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 (limUnder (𝓝[≠] (0 : ℂ)) f)) :=
      Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hdiff hb_sub
    have hcont : ContinuousAt g 0 := continuousAt_update_same.2 htendsto
    have hdiff_g : ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ g z := by
      filter_upwards [hdiff, self_mem_nhdsWithin] with z hz hz0
      have hgz : g =ᶠ[𝓝 z] f := by
        filter_upwards [show ∀ᶠ w in 𝓝 z, w ≠ 0 from IsOpen.mem_nhds isOpen_ne hz0] with w hw
        simp [g, update_of_ne hw]
      exact hz.congr_of_eventuallyEq hgz
    refine ⟨g, Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff_g hcont,
      ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp [g, update_of_ne hz]

/-- Proposition 4.1, punctured-disc bridge form: the owner-level removable-singularity criterion
specialized to a chosen punctured disc around `0`, with boundedness stated by an eventual norm
bound. -/
theorem exists_analytic_extension_at_zero_iff_eventually_bounded_norm
    {f : ℂ → ℂ}
    {r : ℝ} (hr : 0 < r)
    (hpunctured : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) r \ {(0 : ℂ)})) :
    (∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ f =ᶠ[𝓝[≠] (0 : ℂ)] g) ↔
      ∃ M : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖f z‖ ≤ M := by
  have hf : HasIsolatedSingularityAt f (0 : ℂ) :=
    (HasIsolatedSingularityAt.iff_exists_analyticOnNhd_punctured_ball).2 ⟨r, hr, hpunctured⟩
  rw [exists_analytic_extension_at_zero_iff_isBoundedUnder_norm hf]
  constructor
  · intro hbounded
    simpa using hbounded.eventually_le
  · rintro ⟨M, hM⟩
    exact isBoundedUnder_of_eventually_le hM
