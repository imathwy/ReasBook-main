import Mathlib
import cartan.I.section03.«frozen_0008_Definition_I_3_extra_8»
import cartan.I.section03.«frozen_0009_Proposition_5_1»
import cartan.II.section05.«0024_Example_II_1_extra_14»

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the local `Complex.IsLogBranchOn` API and existing `IsSimplyConnected` subset surface were
-- verified directly from repository precedent.

/-- An open set `V` is an extension domain for the logarithm branch `f` on `U` if it contains `U`
and some logarithm branch on `V` restricts to `f` on `U`. -/
def IsLogBranchExtensionDomain (f : ℂ → ℂ) (U V : Set ℂ) : Prop :=
  U ⊆ V ∧ ∃ g : ℂ → ℂ, Complex.IsLogBranchOn g V ∧ Set.EqOn g f U

/-- `V` is a largest extension domain for the logarithm branch `f` on `U` if every other
extension domain is contained in `V`. -/
def IsLargestLogBranchExtensionDomain (f : ℂ → ℂ) (U V : Set ℂ) : Prop :=
  IsLogBranchExtensionDomain f U V ∧
    ∀ W : Set ℂ, IsLogBranchExtensionDomain f U W → W ⊆ V

namespace Complex

/-- Helper for Remark VI.5-extra-10: restricting a logarithm branch to an open connected subset
preserves the branch property. -/
lemma IsLogBranchOn.restrict {f : ℂ → ℂ} {D E : Set ℂ}
    (hf : IsLogBranchOn f D) (hED : E ⊆ D) (hE_open : IsOpen E) (hE_connected : IsConnected E) :
    IsLogBranchOn f E := by
  rcases hf with ⟨_, _, hf_cont, hf_exp⟩
  -- Restrict the continuity and exponential identity to the smaller connected open set.
  exact ⟨hE_open, hE_connected, hf_cont.mono hED, hf_exp.mono hED⟩

/-- Helper for Remark VI.5-extra-10: two logarithm branches on the same connected domain agree
everywhere once they agree at one point. -/
lemma IsLogBranchOn.eqOn_of_eq_at_point {f g : ℂ → ℂ} {D : Set ℂ}
    (hf : IsLogBranchOn f D) (hg : IsLogBranchOn g D) {z₀ : ℂ}
    (hz₀ : z₀ ∈ D) (hfg : f z₀ = g z₀) :
    Set.EqOn f g D := by
  obtain ⟨k, hk⟩ := (IsLogBranchOn.other_iff_eqOn_add_two_pi_I_mul_int hf).1 hg
  have hk_at : f z₀ = f z₀ + k * (2 * Real.pi * Complex.I) := by
    calc
      f z₀ = g z₀ := hfg
      _ = f z₀ + k * (2 * Real.pi * Complex.I) := hk hz₀
  have hk_mul_zero : ((k : ℂ) * (2 * Real.pi * Complex.I)) = 0 := by
    -- Cancel the common branch value at the base point to force the integer period to vanish.
    have hsub := congrArg (fun w : ℂ ↦ w - f z₀) hk_at
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
  have hperiod_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
  have hk_cast_zero : (k : ℂ) = 0 := by
    exact (mul_eq_zero.mp hk_mul_zero).resolve_right hperiod_ne
  have hk_zero : k = 0 := by
    exact Int.cast_injective (α := ℂ) (by simpa using hk_cast_zero)
  -- With zero period, the branch comparison formula collapses to equality everywhere.
  intro z hz
  simpa [hk_zero] using (hk hz).symm

end Complex

/-- Helper for Remark VI.5-extra-10: the shifted slit-plane domain obtained by pulling back the
principal slit plane through negation. -/
abbrev shiftedLogDomain : Set ℂ :=
  {z : ℂ | -z ∈ Complex.slitPlane}

/-- Helper for Remark VI.5-extra-10: the principal logarithm is a branch on the standard slit
plane. -/
lemma principalLog_isLogBranchOn_slitPlane :
    Complex.IsLogBranchOn Complex.log Complex.slitPlane := by
  -- Use the standard slit-plane geometry together with the defining identity of `Complex.log`.
  refine ⟨Complex.isOpen_slitPlane,
    (Complex.starConvex_one_slitPlane.isPathConnected Complex.one_mem_slitPlane).isConnected,
    ?_, ?_⟩
  · simpa using continuousOn_id.clog fun z hz ↦ hz
  · intro z hz
    simpa using Complex.exp_log (Complex.slitPlane_ne_zero hz)

/-- Helper for Remark VI.5-extra-10: the negated slit-plane domain is star-convex at `-1`. -/
lemma shifted_log_domain_starConvex :
    StarConvex ℝ (-(1 : ℂ)) shiftedLogDomain := by
  intro z hz a b ha hb hab
  have hz' : -z ∈ Complex.slitPlane := by
    simpa [shiftedLogDomain] using hz
  have hseg : a • (1 : ℂ) + b • (-z) ∈ Complex.slitPlane :=
    Complex.starConvex_one_slitPlane hz' ha hb hab
  -- Negating the affine combination identifies it with the corresponding slit-plane segment.
  change -(a • (-(1 : ℂ)) + b • z) ∈ Complex.slitPlane
  simpa [smul_neg, neg_add, add_comm, add_left_comm, add_assoc] using hseg

/-- Helper for Remark VI.5-extra-10: the shifted slit-plane domain is simply connected. -/
lemma shifted_log_domain_isSimplyConnected :
    IsSimplyConnected shiftedLogDomain := by
  have hminus_one : (-(1 : ℂ)) ∈ shiftedLogDomain := by
    simp [shiftedLogDomain]
  -- The shifted domain inherits simple connectedness from the star-convex slit-plane model.
  exact isSimplyConnected_of_starConvex hminus_one shifted_log_domain_starConvex

/-- Helper for Remark VI.5-extra-10: the shifted logarithm branch `z ↦ log (-z) + π i` is a
branch of the logarithm on the negated slit-plane domain. -/
lemma shiftedLog_isLogBranchOn :
    Complex.IsLogBranchOn (fun z ↦ Complex.log (-z) + Real.pi * Complex.I) shiftedLogDomain := by
  have hminus_one : (-(1 : ℂ)) ∈ shiftedLogDomain := by
    simp [shiftedLogDomain]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Rewrite the shifted domain as a preimage of `Complex.slitPlane`.
    simpa [shiftedLogDomain] using Complex.isOpen_slitPlane.preimage continuous_neg
  · -- The same star-convex model provides connectedness.
    exact (shifted_log_domain_starConvex.isPathConnected hminus_one).isConnected
  · have hlog : ContinuousOn (fun z ↦ Complex.log (-z)) shiftedLogDomain := by
      refine continuousOn_id.neg.clog ?_
      intro z hz
      simpa [shiftedLogDomain] using hz
    -- Adding the constant period shift keeps the branch continuous.
    simpa using hlog.add continuousOn_const
  · intro z hz
    have hz' : -z ∈ Complex.slitPlane := by
      simpa [shiftedLogDomain] using hz
    -- The shifted branch differs from `log (-z)` by exactly the `π i` factor needed to undo
    -- the extra minus sign.
    calc
      Complex.exp (Complex.log (-z) + Real.pi * Complex.I)
          = Complex.exp (Complex.log (-z)) * Complex.exp (Real.pi * Complex.I) := by
              rw [Complex.exp_add]
      _ = (-z) * (-1) := by
            rw [Complex.exp_log (Complex.slitPlane_ne_zero hz'), Complex.exp_pi_mul_I]
      _ = z := by ring

/-- Remark VI.5-extra-10 (1): there is a branch of the logarithm on an open disk which extends to
two simply connected domains containing both the disk and its image under `z ↦ -z`, but the two
extensions induce different branches on that symmetric image. The excluded-point condition follows
from `Complex.IsLogBranchOn`. -/
theorem exists_incompatible_log_extensions_on_symmetric_domains :
    ∃ (c : ℂ) (r : ℝ) (f : ℂ → ℂ) (V₁ V₂ : Set ℂ) (g₁ g₂ : ℂ → ℂ),
      0 < r ∧
        Complex.IsLogBranchOn f (Metric.ball c r) ∧
        IsSimplyConnected V₁ ∧
        IsSimplyConnected V₂ ∧
        Metric.ball c r ⊆ V₁ ∧
        Metric.ball c r ⊆ V₂ ∧
        (Neg.neg '' Metric.ball c r) ⊆ V₁ ∧
        (Neg.neg '' Metric.ball c r) ⊆ V₂ ∧
        Complex.IsLogBranchOn g₁ V₁ ∧
        Set.EqOn g₁ f (Metric.ball c r) ∧
        Complex.IsLogBranchOn g₂ V₂ ∧
        Set.EqOn g₂ f (Metric.ball c r) ∧
        ∃ z ∈ (Neg.neg '' Metric.ball c r), g₁ z ≠ g₂ z := by
  refine ⟨Complex.I, 1 / 2, Complex.log, Complex.slitPlane, shiftedLogDomain, Complex.log,
    (fun z ↦ Complex.log (-z) + Real.pi * Complex.I), ?_⟩
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have hball_im_gt_half :
      ∀ {z : ℂ}, z ∈ Metric.ball Complex.I (1 / 2) → (1 / 2 : ℝ) < z.im := by
    intro z hz
    have hnorm : ‖z - Complex.I‖ < 1 / 2 := by
      simpa [dist_eq_norm] using hz
    have him_lt : |z.im - 1| < 1 / 2 := by
      have him_le : |z.im - 1| ≤ ‖z - Complex.I‖ := by
        simpa using (Complex.abs_im_le_norm (z - Complex.I))
      exact lt_of_le_of_lt him_le hnorm
    have him_left : -(1 / 2 : ℝ) < z.im - 1 := (abs_lt.mp him_lt).1
    linarith
  have hball_subset_slit : Metric.ball Complex.I (1 / 2) ⊆ Complex.slitPlane := by
    intro z hz
    have hz_im : (1 / 2 : ℝ) < z.im := hball_im_gt_half hz
    rw [Complex.mem_slitPlane_iff]
    right
    linarith
  have hball_subset_shifted : Metric.ball Complex.I (1 / 2) ⊆ shiftedLogDomain := by
    intro z hz
    have hz_im : (1 / 2 : ℝ) < z.im := hball_im_gt_half hz
    change -z ∈ Complex.slitPlane
    rw [Complex.mem_slitPlane_iff]
    right
    have hz_im_ne : z.im ≠ 0 := by linarith
    simpa using neg_ne_zero.mpr hz_im_ne
  have hneg_ball_subset_slit :
      Neg.neg '' Metric.ball Complex.I (1 / 2) ⊆ Complex.slitPlane := by
    rintro z ⟨w, hw, rfl⟩
    have hw_im : (1 / 2 : ℝ) < w.im := hball_im_gt_half hw
    rw [Complex.mem_slitPlane_iff]
    right
    have hw_im_ne : w.im ≠ 0 := by linarith
    simpa using neg_ne_zero.mpr hw_im_ne
  have hneg_ball_subset_shifted :
      Neg.neg '' Metric.ball Complex.I (1 / 2) ⊆ shiftedLogDomain := by
    rintro z ⟨w, hw, rfl⟩
    simpa [shiftedLogDomain] using hball_subset_slit hw
  have hball_connected : IsConnected (Metric.ball Complex.I (1 / 2)) := by
    -- The control disk is convex, hence connected.
    exact (convex_ball Complex.I (1 / 2)).isConnected ⟨Complex.I, Metric.mem_ball_self hr⟩
  have hball_branch :
      Complex.IsLogBranchOn Complex.log (Metric.ball Complex.I (1 / 2)) :=
    principalLog_isLogBranchOn_slitPlane.restrict
      hball_subset_slit Metric.isOpen_ball hball_connected
  have hshifted_ball_branch :
      Complex.IsLogBranchOn
        (fun z ↦ Complex.log (-z) + Real.pi * Complex.I)
        (Metric.ball Complex.I (1 / 2)) :=
    shiftedLog_isLogBranchOn.restrict
      hball_subset_shifted Metric.isOpen_ball hball_connected
  have hshifted_eq_log_at_I :
      (Complex.log (-Complex.I) + Real.pi * Complex.I) = Complex.log Complex.I := by
    -- At the center `I`, the shifted branch matches the principal one.
    rw [Complex.log_I, Complex.log_neg_I]
    ring
  have hshifted_eq_log_on_ball :
      Set.EqOn (fun z ↦ Complex.log (-z) + Real.pi * Complex.I)
        Complex.log (Metric.ball Complex.I (1 / 2)) :=
    Complex.IsLogBranchOn.eqOn_of_eq_at_point
      hshifted_ball_branch hball_branch (Metric.mem_ball_self hr) hshifted_eq_log_at_I
  have hslit_simply : IsSimplyConnected Complex.slitPlane :=
    isSimplyConnected_of_starConvex Complex.one_mem_slitPlane Complex.starConvex_one_slitPlane
  have hdisagree :
      Complex.log (-Complex.I) ≠ Complex.log (-(-Complex.I)) + Real.pi * Complex.I := by
    have hperiod_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
    have hdiff_at_negI :
        (Complex.log (-(-Complex.I)) + Real.pi * Complex.I) - Complex.log (-Complex.I) =
          2 * Real.pi * Complex.I := by
      calc
        (Complex.log (-(-Complex.I)) + Real.pi * Complex.I) - Complex.log (-Complex.I)
            = (Complex.log Complex.I + Real.pi * Complex.I) - Complex.log (-Complex.I) := by simp
        _ = 2 * Real.pi * Complex.I := by
              rw [Complex.log_I, Complex.log_neg_I]
              ring
    intro hEq
    have hzero : (2 * Real.pi * Complex.I : ℂ) = 0 := by
      calc
        (2 * Real.pi * Complex.I : ℂ)
            = (Complex.log (-(-Complex.I)) + Real.pi * Complex.I) - Complex.log (-Complex.I) := by
                symm
                exact hdiff_at_negI
        _ = 0 := by simp [hEq]
    exact hperiod_ne hzero
  -- The explicit witnesses are the principal branch on the slit plane and the shifted branch on
  -- the negated slit plane.
  refine ⟨hr, hball_branch, hslit_simply, shifted_log_domain_isSimplyConnected,
    hball_subset_slit, hball_subset_shifted, hneg_ball_subset_slit, hneg_ball_subset_shifted,
    principalLog_isLogBranchOn_slitPlane, ?_, shiftedLog_isLogBranchOn, hshifted_eq_log_on_ball,
    ?_⟩
  · intro z hz
    rfl
  · refine ⟨-Complex.I, ?_, hdisagree⟩
    exact ⟨Complex.I, Metric.mem_ball_self hr, by simp⟩

/-- Remark VI.5-extra-10 (2): for a branch of the logarithm on an open disk, there need not exist
any largest connected open set to which the branch extends holomorphically. The excluded-point
condition follows from `Complex.IsLogBranchOn`. -/
theorem exists_log_branch_without_largest_extension_domain :
    ∃ (c : ℂ) (r : ℝ) (f : ℂ → ℂ),
      0 < r ∧
        Complex.IsLogBranchOn f (Metric.ball c r) ∧
        ¬ ∃ V : Set ℂ, IsLargestLogBranchExtensionDomain f (Metric.ball c r) V := by
  rcases exists_incompatible_log_extensions_on_symmetric_domains with
    ⟨c, r, f, V₁, V₂, g₁, g₂, hr, hf, _, _, hU_subset_V₁, hU_subset_V₂, hneg_subset_V₁,
      hneg_subset_V₂, hg₁, hg₁U, hg₂, hg₂U, ⟨z, hzneg, hzneq⟩⟩
  refine ⟨c, r, f, hr, hf, ?_⟩
  intro hlargest
  rcases hlargest with ⟨V, ⟨hU_subset_V, g, hgV, hgU⟩, hmax⟩
  have hV₁_ext : IsLogBranchExtensionDomain f (Metric.ball c r) V₁ := by
    exact ⟨hU_subset_V₁, ⟨g₁, hg₁, hg₁U⟩⟩
  have hV₂_ext : IsLogBranchExtensionDomain f (Metric.ball c r) V₂ := by
    exact ⟨hU_subset_V₂, ⟨g₂, hg₂, hg₂U⟩⟩
  have hV₁_subset_V : V₁ ⊆ V := hmax V₁ hV₁_ext
  have hV₂_subset_V : V₂ ⊆ V := hmax V₂ hV₂_ext
  have hc_mem_ball : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  have hg_on_V₁ : Complex.IsLogBranchOn g V₁ :=
    hgV.restrict hV₁_subset_V hg₁.1 hg₁.2.1
  have hg_on_V₂ : Complex.IsLogBranchOn g V₂ :=
    hgV.restrict hV₂_subset_V hg₂.1 hg₂.2.1
  have hg_eq_g₁_at_c : g c = g₁ c := by
    -- All candidate extensions must agree with the original branch on the base disk.
    calc
      g c = f c := hgU hc_mem_ball
      _ = g₁ c := (hg₁U hc_mem_ball).symm
  have hg_eq_g₂_at_c : g c = g₂ c := by
    calc
      g c = f c := hgU hc_mem_ball
      _ = g₂ c := (hg₂U hc_mem_ball).symm
  have hg_eq_g₁ : Set.EqOn g g₁ V₁ :=
    Complex.IsLogBranchOn.eqOn_of_eq_at_point
      hg_on_V₁ hg₁ (hU_subset_V₁ hc_mem_ball) hg_eq_g₁_at_c
  have hg_eq_g₂ : Set.EqOn g g₂ V₂ :=
    Complex.IsLogBranchOn.eqOn_of_eq_at_point
      hg_on_V₂ hg₂ (hU_subset_V₂ hc_mem_ball) hg_eq_g₂_at_c
  have hzV₁ : z ∈ V₁ := hneg_subset_V₁ hzneg
  have hzV₂ : z ∈ V₂ := hneg_subset_V₂ hzneg
  apply hzneq
  -- The hypothetical largest extension would force the two incompatible continuations to agree.
  calc
    g₁ z = g z := (hg_eq_g₁ hzV₁).symm
    _ = g₂ z := hg_eq_g₂ hzV₂
