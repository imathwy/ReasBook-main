import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the proof is phrased directly through the canonical branch `Complex.log` on
-- `Complex.slitPlane`, the owner theorem
-- `AnalyticOnNhd.eq_re_add_const_mul_I_of_re_eq_const`, and the canonical one-sided boundary
-- limits of `Complex.log` on the negative real axis.

open Complex Filter Set Topology

/-- Remark IV.3-extra-4. On the punctured complex plane, the harmonic function
`z ↦ log ‖z‖` is not the real part of any holomorphic function defined on the whole domain. -/
theorem not_exists_analyticOnNhd_re_eq_log_norm_on_punctured_plane :
    ¬ ∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f ({0}ᶜ : Set ℂ) ∧
        Set.EqOn (fun z ↦ (f z).re) (fun z : ℂ ↦ Real.log ‖z‖) ({0}ᶜ : Set ℂ) := by
  rintro ⟨f, hf, hEq⟩
  let upper : Set ℂ := {z : ℂ | 0 < z.im}
  let lower : Set ℂ := {z : ℂ | z.im < 0}
  have hminus_one : (-1 : ℂ) ∈ ({0}ᶜ : Set ℂ) := by simp
  have hslit : AnalyticOnNhd ℂ (fun z ↦ f z - log z) slitPlane := by
    refine (hf.mono fun z hz ↦ slitPlane_ne_zero hz).sub ?_
    exact analyticOnNhd_id.clog fun z hz ↦ hz
  have hslit_re : ∀ z ∈ slitPlane, ((f z - log z).re : ℝ) = 0 := by
    intro z hz
    have hz0 : z ∈ ({0}ᶜ : Set ℂ) := by simpa using slitPlane_ne_zero hz
    calc
      ((f z - log z).re : ℝ) = (f z).re - Real.log ‖z‖ := by simp [Complex.log_re]
      _ = 0 := by linarith [hEq hz0]
  obtain ⟨c, hc⟩ := AnalyticOnNhd.eq_re_add_const_mul_I_of_re_eq_const hslit hslit_re
    isOpen_slitPlane
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected
  have hbranch : EqOn f (fun z ↦ log z + c * I) slitPlane := by
    intro z hz
    specialize hc z hz
    simpa [add_comm] using sub_eq_iff_eq_add'.mp (by simpa using hc)
  have hupper_subset : upper ⊆ slitPlane := by
    intro z hz
    have hz_im : 0 < z.im := by simpa [upper] using hz
    simp [mem_slitPlane_iff, hz_im.ne']
  have hlower_subset : lower ⊆ slitPlane := by
    intro z hz
    have hz_im : z.im < 0 := by simpa [lower] using hz
    simp [mem_slitPlane_iff, hz_im.ne]
  have hEq_upper : EqOn f (fun z ↦ log z + c * I) upper := fun z hz ↦ hbranch (hupper_subset hz)
  have hEq_lower : EqOn f (fun z ↦ log z + c * I) lower := fun z hz ↦ hbranch (hlower_subset hz)
  have hcont : ContinuousAt f (-1 : ℂ) := (hf (-1) hminus_one).continuousAt
  have hupper_f : Tendsto (fun z ↦ log z + c * I) (𝓝[upper] (-1 : ℂ)) (𝓝 (f (-1))) :=
    (tendsto_congr' hEq_upper.eventuallyEq_nhdsWithin).1 hcont.continuousWithinAt.tendsto
  have hlower_f : Tendsto (fun z ↦ log z + c * I) (𝓝[lower] (-1 : ℂ)) (𝓝 (f (-1))) :=
    (tendsto_congr' hEq_lower.eventuallyEq_nhdsWithin).1 hcont.continuousWithinAt.tendsto
  have hminus_one_re_neg : ((-1 : ℂ)).re < 0 := by norm_num
  have hminus_one_im_zero : ((-1 : ℂ)).im = 0 := by simp
  have hlog_upper_nonneg :
      Tendsto log (𝓝[{z : ℂ | 0 ≤ z.im}] (-1 : ℂ)) (𝓝 (Real.pi * I)) := by
    simpa using
      tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hminus_one_re_neg hminus_one_im_zero
  have hlog_upper : Tendsto log (𝓝[upper] (-1 : ℂ)) (𝓝 (Real.pi * I)) :=
    hlog_upper_nonneg.mono_left <| nhdsWithin_mono _ fun z hz ↦ by
      have hz_im : 0 < z.im := by simpa [upper] using hz
      simpa using hz_im.le
  have hlog_lower : Tendsto log (𝓝[lower] (-1 : ℂ)) (𝓝 (-Real.pi * I)) := by
    simpa [lower] using
      tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hminus_one_re_neg hminus_one_im_zero
  have hupper_rhs :
      Tendsto (fun z ↦ log z + c * I) (𝓝[upper] (-1 : ℂ)) (𝓝 (Real.pi * I + c * I)) := by
    simpa using hlog_upper.add tendsto_const_nhds
  have hlower_rhs :
      Tendsto (fun z ↦ log z + c * I) (𝓝[lower] (-1 : ℂ)) (𝓝 (-Real.pi * I + c * I)) := by
    simpa using hlog_lower.add tendsto_const_nhds
  have hupper_neBot : NeBot (𝓝[upper] (-1 : ℂ)) := by
    rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
    intro ε hε
    refine ⟨-1 + (ε / 2) * I, ?_, ?_⟩
    · simp [upper, hε]
    · have hhalf : |ε| / 2 < ε := by
        rw [abs_of_nonneg hε.le]
        nlinarith
      simpa [dist_eq_norm] using hhalf
  have hlower_neBot : NeBot (𝓝[lower] (-1 : ℂ)) := by
    rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
    intro ε hε
    refine ⟨-1 - (ε / 2) * I, ?_, ?_⟩
    · simp [lower, hε]
    · have hhalf : |ε| / 2 < ε := by
        rw [abs_of_nonneg hε.le]
        nlinarith
      simpa [dist_eq_norm] using hhalf
  have hupper_val : f (-1) = Real.pi * I + c * I :=
    tendsto_nhds_unique' hupper_neBot hupper_f hupper_rhs
  have hlower_val : f (-1) = -Real.pi * I + c * I :=
    tendsto_nhds_unique' hlower_neBot hlower_f hlower_rhs
  have him : -Real.pi + c = Real.pi + c := by
    simpa using congrArg Complex.im (hlower_val.symm.trans hupper_val)
  linarith [Real.pi_pos]
