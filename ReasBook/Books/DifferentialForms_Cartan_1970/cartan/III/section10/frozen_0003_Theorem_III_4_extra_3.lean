import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section06.«0009_Example_II_2_extra_3»
import DifferentialForms_Cartan_1970.cartan.III.section10.«0002_Definition_III_4_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology
open Metric

noncomputable section

-- Proof sketch: choose intermediate circles inside the annulus, define the coefficients by
-- Cauchy integrals on those circles, expand the Cauchy kernels into positive and negative power
-- series on each closed subannulus, and use normal convergence to identify the resulting Laurent
-- series with `f`.
/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: the open annulus
`ρ₂ < |z| < ρ₁` is an open subset of `ℂ`. -/
lemma isOpen_complexOpenAnnulus (ρ₂ ρ₁ : ENNReal) : IsOpen (complexOpenAnnulus ρ₂ ρ₁) := by
  -- Both defining norm inequalities are open conditions, so their conjunction is open as well.
  simpa [complexOpenAnnulus] using
    (isOpen_lt (continuous_const : Continuous fun _ : ℂ ↦ ρ₂)
      (ENNReal.continuous_coe.comp continuous_nnnorm)).inter
      (isOpen_lt (ENNReal.continuous_coe.comp continuous_nnnorm)
        (continuous_const : Continuous fun _ : ℂ ↦ ρ₁))

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: a circle whose radius lies
strictly between `ρ₂` and `ρ₁` is contained in the annulus `ρ₂ < ‖z‖ < ρ₁`. -/
lemma sphere_subset_complexOpenAnnulus_of_lt_lt
    {ρ₂ ρ₁ R : NNReal} (hρ₂ : ρ₂ < R) (hρ₁ : R < ρ₁) :
    sphere (0 : ℂ) (R : ℝ) ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
  -- Points on the radius-`R` circle satisfy the defining annulus inequalities exactly because
  -- their norm is `R`.
  intro z hz
  have hzR : ‖z‖ = (R : ℝ) := by
    simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
  have hzR' : ‖z‖₊ = R := by
    exact NNReal.coe_injective (by simpa using hzR)
  change (ρ₂ : ENNReal) < ‖z‖₊ ∧ ‖z‖₊ < (ρ₁ : ENNReal)
  constructor
  · simpa [hzR'] using (show (ρ₂ : ENNReal) < (R : ENNReal) by exact_mod_cast hρ₂)
  · simpa [hzR'] using (show (R : ENNReal) < (ρ₁ : ENNReal) by exact_mod_cast hρ₁)

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: the outer Cauchy transform over
the radius-`R` circle. -/
noncomputable def circleInnerPiece (f : ℂ → ℂ) (R : NNReal) : ℂ → ℂ :=
  fun z ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ t in C(0, (R : ℝ)), (t - z)⁻¹ • f t

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: the Cauchy transform over a
circle inside the annulus is analytic on the enclosed disc. -/
lemma circleInnerPiece_analyticOnNhd
    {ρ₂ ρ₁ R : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁))
    (hρ₂ : ρ₂ < R) (hρ₁ : R < ρ₁) :
    AnalyticOnNhd ℂ (circleInnerPiece f R) (ball (0 : ℂ) R) := by
  -- The boundary values are continuous on the chosen circle because annulus analyticity gives
  -- continuity on every smaller closed subset.
  have hsphere :
      sphere (0 : ℂ) (R : ℝ) ⊆ complexOpenAnnulus ρ₂ ρ₁ :=
    sphere_subset_complexOpenAnnulus_of_lt_lt hρ₂ hρ₁
  have hcont : ContinuousOn f (sphere (0 : ℂ) (R : ℝ)) :=
    hf.continuousOn.mono hsphere
  have hcircle : CircleIntegrable f 0 (R : ℝ) :=
    hcont.circleIntegrable R.2
  have hR0 : 0 < R := lt_of_le_of_lt ρ₂.2 hρ₂
  -- Mathlib's Cauchy-integral power-series theorem gives analyticity on the whole disc.
  convert
      (hasFPowerSeriesOn_cauchy_integral (c := (0 : ℂ)) (R := R) hcircle hR0).analyticOnNhd using
    1
  ext z
  simp

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: the inner-circle Cauchy
transform that will supply the negative Laurent part. -/
noncomputable def circleOuterPiece (f : ℂ → ℂ) (r : NNReal) : ℂ → ℂ :=
  fun z ↦ -((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ t in C(0, (r : ℝ)), (t - z)⁻¹ • f t)

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: on every overlap annulus, the
outer-circle and inner-circle Cauchy pieces add back up to the original function. -/
lemma annulus_circle_piece_sum_eq
    {ρ₂ ρ₁ r R : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁))
    (hρ₂r : ρ₂ < r) (hrR : r < R) (hRρ₁ : R < ρ₁)
    {z : ℂ} (hzr : (r : ℝ) < ‖z‖) (hzR : ‖z‖ < (R : ℝ)) :
    f z = circleInnerPiece f R z + circleOuterPiece f r z := by
  let closedAnnulus : Set ℂ := closedBall (0 : ℂ) (R : ℝ) \ ball (0 : ℂ) (r : ℝ)
  let puncturedAnnulus : Set ℂ := ball (0 : ℂ) (R : ℝ) \ closedBall (0 : ℂ) (r : ℝ)
  let badSet : Set ℂ := {z}
  have hzAnn : z ∈ complexOpenAnnulus ρ₂ ρ₁ := by
    -- The evaluation point lies in the geometric overlap where the annulus formula applies.
    change (ρ₂ : ENNReal) < ‖z‖₊ ∧ ‖z‖₊ < (ρ₁ : ENNReal)
    constructor
    · exact_mod_cast lt_trans hρ₂r hzr
    · exact_mod_cast lt_trans hzR hRρ₁
  have hr0 : 0 < (r : ℝ) := by
    exact_mod_cast lt_of_le_of_lt ρ₂.2 hρ₂r
  have hle : (r : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hrR.le
  have hz_mem_ballR : z ∈ ball (0 : ℂ) (R : ℝ) := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hzR
  have hz_mem_closedBallR : z ∈ closedBall (0 : ℂ) (R : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hzR.le
  have hz_not_closedBallr : z ∉ closedBall (0 : ℂ) (r : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using not_le_of_gt hzr
  have hsphereR :
      sphere (0 : ℂ) (R : ℝ) ⊆ complexOpenAnnulus ρ₂ ρ₁ :=
    sphere_subset_complexOpenAnnulus_of_lt_lt (R := R) (lt_trans hρ₂r hrR) hRρ₁
  have hspherer :
      sphere (0 : ℂ) (r : ℝ) ⊆ complexOpenAnnulus ρ₂ ρ₁ :=
    sphere_subset_complexOpenAnnulus_of_lt_lt (R := r) hρ₂r (lt_trans hrR hRρ₁)
  have hclosedAnnulus_subset : closedAnnulus ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
    -- Every point in the geometric closed annulus satisfies the same two strict bounds.
    intro w hw
    rcases hw with ⟨hwR, hwr⟩
    have hwr' : (r : ℝ) ≤ ‖w‖ := by
      have : ¬ ‖w‖ < (r : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hwr
      exact le_of_not_gt this
    have hwR' : ‖w‖ ≤ (R : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hwR
    change (ρ₂ : ENNReal) < ‖w‖₊ ∧ ‖w‖₊ < (ρ₁ : ENNReal)
    constructor
    · exact_mod_cast lt_of_lt_of_le hρ₂r hwr'
    · exact_mod_cast lt_of_le_of_lt hwR' hRρ₁
  have hpuncturedAnnulus_subset : puncturedAnnulus ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
    -- The punctured geometric annulus inherits the same strict inequalities.
    intro w hw
    rcases hw with ⟨hwR, hwr⟩
    have hwr' : (r : ℝ) < ‖w‖ := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hwr
    have hwR' : ‖w‖ < (R : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hwR
    change (ρ₂ : ENNReal) < ‖w‖₊ ∧ ‖w‖₊ < (ρ₁ : ENNReal)
    constructor
    · exact_mod_cast lt_trans hρ₂r hwr'
    · exact_mod_cast lt_trans hwR' hRρ₁
  have hclosedAnnulus_nhds : closedAnnulus ∈ 𝓝 z := by
    -- Near `z`, we remain inside the closed annulus because `z` is strictly between the two
    -- boundary circles.
    have hclosed : closedBall (0 : ℂ) (R : ℝ) ∈ 𝓝 z :=
      Metric.closedBall_mem_nhds_of_mem hz_mem_ballR
    have hcompl : (closedBall (0 : ℂ) (r : ℝ))ᶜ ∈ 𝓝 z :=
      isClosed_closedBall.isOpen_compl.mem_nhds hz_not_closedBallr
    refine Filter.mem_of_superset (Filter.inter_mem hclosed hcompl) ?_
    intro w hw
    rcases hw with ⟨hwR, hwr⟩
    exact ⟨hwR, fun hwball ↦ hwr (ball_subset_closedBall hwball)⟩
  have hcont_closedAnnulus : ContinuousOn f closedAnnulus :=
    hf.continuousOn.mono hclosedAnnulus_subset
  have hcont_outer : ContinuousOn f (sphere (0 : ℂ) (R : ℝ)) :=
    hf.continuousOn.mono hsphereR
  have hcont_inner : ContinuousOn f (sphere (0 : ℂ) (r : ℝ)) :=
    hf.continuousOn.mono hspherer
  have hdslope_cont :
      ContinuousOn (dslope f z) closedAnnulus := by
    -- Replacing the pole by `dslope` removes the singularity at `z`.
    exact
      (continuousOn_dslope hclosedAnnulus_nhds).2
        ⟨hcont_closedAnnulus, (hf z hzAnn).differentiableAt⟩
  have hdslope_diff :
      ∀ w ∈ puncturedAnnulus \ badSet, DifferentiableAt ℂ (dslope f z) w := by
    -- Away from the removed point `z`, `dslope` has the same differentiability as `f`.
    intro w hw
    have hw_ne : w ≠ z := by
      simpa [badSet] using hw.2
    exact
      (differentiableAt_dslope_of_ne hw_ne).2
        ((hf w (hpuncturedAnnulus_subset hw.1)).differentiableAt)
  have hdslope_circle :
      (∮ w in C(0, (R : ℝ)), dslope f z w) =
        ∮ w in C(0, (r : ℝ)), dslope f z w := by
    -- Annulus Cauchy-Goursat applies to the regularized kernel `dslope f z`.
    exact
      Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr0 hle
        (Set.countable_singleton z) hdslope_cont hdslope_diff
  have houter_ne : ∀ w ∈ sphere (0 : ℂ) (R : ℝ), w ≠ z := by
    intro w hw
    have hw_norm : ‖w‖ = (R : ℝ) := by
      simpa using mem_sphere_iff_norm.mp hw
    exact fun hwz ↦ (ne_of_lt hzR) (by simpa [hwz] using hw_norm)
  have hinner_ne : ∀ w ∈ sphere (0 : ℂ) (r : ℝ), w ≠ z := by
    intro w hw
    have hw_norm : ‖w‖ = (r : ℝ) := by
      simpa using mem_sphere_iff_norm.mp hw
    exact fun hwz ↦ (ne_of_lt hzr) (by simpa [hwz] using hw_norm.symm)
  have houter_inv_cont :
      ContinuousOn (fun w : ℂ ↦ (w - z)⁻¹) (sphere (0 : ℂ) (R : ℝ)) :=
    ((continuousOn_id.sub continuousOn_const).inv₀ fun w hw ↦ sub_ne_zero.2 (houter_ne w hw))
  have hinner_inv_cont :
      ContinuousOn (fun w : ℂ ↦ (w - z)⁻¹) (sphere (0 : ℂ) (r : ℝ)) :=
    ((continuousOn_id.sub continuousOn_const).inv₀ fun w hw ↦ sub_ne_zero.2 (hinner_ne w hw))
  have houter_kernel_integrable :
      CircleIntegrable (fun w : ℂ ↦ (w - z)⁻¹ • f w) 0 (R : ℝ) :=
    (houter_inv_cont.smul hcont_outer).circleIntegrable R.2
  have houter_const_integrable :
      CircleIntegrable (fun w : ℂ ↦ (w - z)⁻¹ • f z) 0 (R : ℝ) :=
    (houter_inv_cont.smul continuousOn_const).circleIntegrable R.2
  have hinner_kernel_integrable :
      CircleIntegrable (fun w : ℂ ↦ (w - z)⁻¹ • f w) 0 (r : ℝ) :=
    (hinner_inv_cont.smul hcont_inner).circleIntegrable r.2
  have hinner_const_integrable :
      CircleIntegrable (fun w : ℂ ↦ (w - z)⁻¹ • f z) 0 (r : ℝ) :=
    (hinner_inv_cont.smul continuousOn_const).circleIntegrable r.2
  have houter_dslope :
      (∮ w in C(0, (R : ℝ)), dslope f z w) =
        (∮ w in C(0, (R : ℝ)), (w - z)⁻¹ • f w) -
          ∮ w in C(0, (R : ℝ)), (w - z)⁻¹ • f z := by
    -- On the outer circle, `dslope` is literally the difference of the singular kernel term and
    -- its constant part.
    rw [← circleIntegral.integral_sub houter_kernel_integrable houter_const_integrable]
    refine circleIntegral.integral_congr R.2 ?_
    intro w hw
    calc
      dslope f z w = (w - z)⁻¹ • (f w - f z) := by
        rw [dslope_of_ne _ (houter_ne w hw), slope_def_module]
      _ = (w - z)⁻¹ • f w - (w - z)⁻¹ • f z := smul_sub _ _ _
  have hinner_dslope :
      (∮ w in C(0, (r : ℝ)), dslope f z w) =
        (∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f w) -
          ∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f z := by
    -- The same `dslope` decomposition works on the inner circle.
    rw [← circleIntegral.integral_sub hinner_kernel_integrable hinner_const_integrable]
    refine circleIntegral.integral_congr r.2 ?_
    intro w hw
    calc
      dslope f z w = (w - z)⁻¹ • (f w - f z) := by
        rw [dslope_of_ne _ (hinner_ne w hw), slope_def_module]
      _ = (w - z)⁻¹ • f w - (w - z)⁻¹ • f z := smul_sub _ _ _
  have houter_const :
      ∮ w in C(0, (R : ℝ)), (w - z)⁻¹ • f z = (2 * Real.pi * Complex.I : ℂ) • f z := by
    -- The outer constant term is exactly the ordinary Cauchy kernel integral through `z`.
    calc
      ∮ w in C(0, (R : ℝ)), (w - z)⁻¹ • f z
        = (∮ w in C(0, (R : ℝ)), (w - z)⁻¹) * f z := by
            simpa [smul_eq_mul] using
              (circleIntegral.integral_smul_const (f := fun w : ℂ ↦ (w - z)⁻¹) (a := f z)
                (c := (0 : ℂ)) (R := (R : ℝ)))
      _ = (2 * Real.pi * Complex.I : ℂ) * f z := by
            rw [circleIntegral.integral_sub_inv_of_mem_ball
              (c := (0 : ℂ)) (w := z) (R := (R : ℝ)) hz_mem_ballR]
  have hinner_const :
      ∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f z = 0 := by
    -- On the inner circle, the kernel pole lies outside the closed disc, so the integral vanishes.
    have hkernel_inner :
        ∮ w in C(0, (r : ℝ)), (w - z)⁻¹ = 0 := by
      simpa [one_div, div_eq_inv_mul, mul_assoc, mul_left_comm, mul_comm] using
        circleIntegral_div_sub_eq_zero_of_not_mem_closedBall
          (c := (0 : ℂ)) (a := z) (R := (r : ℝ)) r.2
          (diffContOnCl_const : DiffContOnCl ℂ (fun _ : ℂ ↦ (1 : ℂ)) (ball (0 : ℂ) (r : ℝ)))
          hz_not_closedBallr
    calc
      ∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f z
        = (∮ w in C(0, (r : ℝ)), (w - z)⁻¹) * f z := by
            simpa [smul_eq_mul] using
              (circleIntegral.integral_smul_const (f := fun w : ℂ ↦ (w - z)⁻¹) (a := f z)
                (c := (0 : ℂ)) (R := (r : ℝ)))
      _ = 0 := by
            rw [hkernel_inner, zero_mul]
  have hdiff :
      (∮ w in C(0, (R : ℝ)), (w - z)⁻¹ • f w) -
        ∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f w = (2 * Real.pi * Complex.I : ℂ) • f z := by
    -- Comparing the outer and inner `dslope` integrals isolates exactly the residue term.
    have houter_minus_inner :
        (∮ w in C(0, (R : ℝ)), (w - z)⁻¹ • f w) - (2 * Real.pi * Complex.I : ℂ) • f z
          = ∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f w := by
      calc
        (∮ w in C(0, (R : ℝ)), (w - z)⁻¹ • f w) - (2 * Real.pi * Complex.I : ℂ) • f z
            = (∮ w in C(0, (R : ℝ)), (w - z)⁻¹ • f w) -
                ∮ w in C(0, (R : ℝ)), (w - z)⁻¹ • f z := by rw [houter_const]
        _ = ∮ w in C(0, (R : ℝ)), dslope f z w := by rw [houter_dslope]
        _ = ∮ w in C(0, (r : ℝ)), dslope f z w := hdslope_circle
        _ = (∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f w) -
              ∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f z := by rw [hinner_dslope]
        _ = ∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f w := by rw [hinner_const, sub_zero]
    rw [← houter_minus_inner]
    ring
  have hdiff' :
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ((∮ w in C(0, (R : ℝ)), (w - z)⁻¹ • f w) -
            ∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f w)
        = f z := by
    -- Normalize by `2π i`.
    set a : ℂ := (2 * Real.pi * Complex.I : ℂ) with ha_def
    have ha : a ≠ 0 := by
      have htwoPi : (2 * (↑Real.pi : ℂ)) ≠ 0 := by
        norm_num [Real.pi_ne_zero]
      exact mul_ne_zero htwoPi Complex.I_ne_zero
    rw [hdiff, smul_eq_mul]
    have hnorm : a⁻¹ * (a * f z) = f z :=
      inv_mul_cancel_left₀ ha (f z)
    simpa [a, mul_assoc] using hnorm
  -- Unfold the two Cauchy pieces and rearrange the normalized integral identity.
  have hmain :
      circleInnerPiece f R z + circleOuterPiece f r z
        = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
            ((∮ w in C(0, (R : ℝ)), (w - z)⁻¹ • f w) -
              ∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f w) := by
    simp [circleInnerPiece, circleOuterPiece, smul_eq_mul, sub_eq_add_neg, left_distrib,
      mul_assoc, mul_left_comm, mul_comm]
  calc
    f z = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ((∮ w in C(0, (R : ℝ)), (w - z)⁻¹ • f w) -
          ∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f w) := hdiff'.symm
    _ = circleInnerPiece f R z + circleOuterPiece f r z := by
        rw [hmain]

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: two analytic extensions of the
same punctured-ball function must agree on the whole ball. -/
lemma analytic_extension_on_ball_unique
    {ρ : ℝ} (hρ : 0 < ρ) {f g h : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball (0 : ℂ) ρ))
    (hh : AnalyticOnNhd ℂ h (ball (0 : ℂ) ρ))
    (hfg : Set.EqOn f g (ball (0 : ℂ) ρ \ {(0 : ℂ)}))
    (hfh : Set.EqOn f h (ball (0 : ℂ) ρ \ {(0 : ℂ)})) :
    Set.EqOn g h (ball (0 : ℂ) ρ) := by
  let U := ball (0 : ℂ) ρ
  have hgh : Set.EqOn g h (U \ {(0 : ℂ)}) := by
    intro z hz
    exact (hfg hz).symm.trans (hfh hz)
  have hfrequently : ∃ᶠ z in 𝓝[≠] (0 : ℂ), g z = h z := by
    -- The punctured ball itself is a punctured neighborhood of `0` where the two extensions
    -- agree pointwise.
    refine Filter.Eventually.frequently ?_
    filter_upwards [inter_mem_nhdsWithin ({(0 : ℂ)}ᶜ) (Metric.ball_mem_nhds (0 : ℂ) hρ)] with z hz
    rcases hz with ⟨hz0, hzU⟩
    exact hgh ⟨hzU, hz0⟩
  -- Route correction: this is the local identity-principle bridge used when equality is first
  -- proved only on a punctured neighborhood.
  exact hg.eqOn_of_preconnected_of_frequently_eq hh
    (by simpa [U] using (convex_ball (0 : ℂ) ρ).isPreconnected)
    (Metric.mem_ball_self hρ) hfrequently

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: if two outer Cauchy circles
stay inside the annulus, then their inner analytic pieces agree on the smaller disc. -/
lemma circleInnerPiece_eq_on_smallerBall
    {ρ₂ ρ₁ r R₁ R₂ : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁))
    (hρ₂r : ρ₂ < r) (hrR₁ : r < R₁) (hR₁R₂ : R₁ ≤ R₂) (hR₂ρ₁ : R₂ < ρ₁) :
    Set.EqOn (circleInnerPiece f R₁) (circleInnerPiece f R₂) (ball (0 : ℂ) (R₁ : ℝ)) := by
  have hR₁ρ₁ : R₁ < ρ₁ := lt_of_le_of_lt hR₁R₂ hR₂ρ₁
  have hanalytic₁ :
      AnalyticOnNhd ℂ (circleInnerPiece f R₁) (ball (0 : ℂ) (R₁ : ℝ)) :=
    circleInnerPiece_analyticOnNhd hf (lt_trans hρ₂r hrR₁) hR₁ρ₁
  have hanalytic₂_big :
      AnalyticOnNhd ℂ (circleInnerPiece f R₂) (ball (0 : ℂ) (R₂ : ℝ)) :=
    circleInnerPiece_analyticOnNhd hf (lt_trans hρ₂r (lt_of_lt_of_le hrR₁ hR₁R₂)) hR₂ρ₁
  have hanalytic₂ :
      AnalyticOnNhd ℂ (circleInnerPiece f R₂) (ball (0 : ℂ) (R₁ : ℝ)) :=
    hanalytic₂_big.mono fun z hz ↦ by
      simp only [Metric.mem_ball, dist_eq_norm, sub_zero] at hz ⊢
      exact lt_of_lt_of_le hz hR₁R₂
  let overlap : Set ℂ := ball (0 : ℂ) (R₁ : ℝ) \ closedBall (0 : ℂ) (r : ℝ)
  have hoverlap_eq :
      Set.EqOn (circleInnerPiece f R₁) (circleInnerPiece f R₂) overlap := by
    intro z hz
    have hzr : (r : ℝ) < ‖z‖ := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz.2
    have hzR₁ : ‖z‖ < (R₁ : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hz.1
    have hzR₂ : ‖z‖ < (R₂ : ℝ) := lt_of_lt_of_le hzR₁ hR₁R₂
    have hdecomp₁ :=
      annulus_circle_piece_sum_eq (f := f) (ρ₂ := ρ₂) (ρ₁ := ρ₁) (r := r) (R := R₁)
        hf hρ₂r hrR₁ hR₁ρ₁ hzr hzR₁
    have hdecomp₂ :=
      annulus_circle_piece_sum_eq (f := f) (ρ₂ := ρ₂) (ρ₁ := ρ₁) (r := r) (R := R₂)
        hf hρ₂r (lt_of_lt_of_le hrR₁ hR₁R₂) hR₂ρ₁ hzr hzR₂
    exact add_right_cancel (hdecomp₁.symm.trans hdecomp₂)
  rcases exists_between hrR₁ with ⟨s, hrs, hsR₁⟩
  have hs_mem_overlap : (s : ℂ) ∈ overlap := by
    constructor
    · simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hsR₁
    · simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using not_le_of_gt hrs
  have hoverlap_open : IsOpen overlap :=
    Metric.isOpen_ball.sdiff isClosed_closedBall
  have hEvent :
      circleInnerPiece f R₁ =ᶠ[𝓝 (s : ℂ)] circleInnerPiece f R₂ := by
    -- The overlap annulus is an open neighborhood where the two Cauchy models agree pointwise.
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨overlap, hoverlap_open.mem_nhds hs_mem_overlap, hoverlap_eq⟩
  -- Route correction: the positive-radius comparison is proved by analytic continuation from the
  -- nonempty overlap annulus, not by manipulating contour coefficients directly.
  exact hanalytic₁.eqOn_of_preconnected_of_eventuallyEq hanalytic₂
    Metric.isPreconnected_ball hs_mem_overlap.1 hEvent

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: if `r < ‖z‖`, then `z⁻¹`
lies in the reciprocal ball of radius `r⁻¹`. -/
lemma inv_mem_ball_zero_inv_radius_of_lt
    {r : NNReal} {z : ℂ} (hr : 0 < r) (hrz : r < ‖z‖₊) :
    z⁻¹ ∈ ball (0 : ℂ) (((r⁻¹ : NNReal) : ℝ)) := by
  -- Inverting the strict norm inequality turns `r < ‖z‖` into `‖z⁻¹‖ < r⁻¹`.
  have hz0 : z ≠ 0 := by
    intro hz0
    have hrz0 : r < 0 := by
      have hrz0 := hrz
      rw [hz0] at hrz0
      simp at hrz0
    exact (not_lt_of_ge r.2) hrz0
  rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_inv]
  have hrz' : (r : ℝ) < ‖z‖ := by
    exact_mod_cast hrz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hrpos : 0 < (r : ℝ) := by
    exact_mod_cast hr
  simpa [one_div] using (one_div_lt_one_div hzpos hrpos).2 hrz'

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: the reciprocal version of the
inner-circle Cauchy piece used for the negative Laurent tail. -/
noncomputable def outerReciprocalPiece (f : ℂ → ℂ) (r : NNReal) : ℂ → ℂ :=
  fun w ↦ w⁻¹ * circleOuterPiece f r (w⁻¹)

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: inversion carries the
reciprocal-radius circle back to the original radius-`r` circle. -/
lemma inv_mem_sphere_of_mem_reciprocal_sphere
    {r : NNReal} {w : ℂ}
    (hw : w ∈ sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ))) :
    w⁻¹ ∈ sphere (0 : ℂ) (r : ℝ) := by
  -- On the reciprocal circle, taking norms after inversion restores the original radius `r`.
  have hw' : ‖w‖ = (((r⁻¹ : NNReal) : ℝ)) := by
    simpa [sub_zero] using hw
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  rw [norm_inv, hw']
  simp [NNReal.coe_inv]

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: on the punctured reciprocal
disc, the raw outer kernel is exactly the regularized kernel `(1 - w * t)⁻¹`. -/
lemma outerReciprocalKernel_eq_regularized
    {w t : ℂ} (hw : w ≠ 0) :
    -(w⁻¹ * (t - w⁻¹)⁻¹) = (1 - w * t)⁻¹ := by
  -- Route correction: normalize the negative-tail kernel before asking for an analytic extension
  -- at `0`; the raw `w⁻¹ * (t - w⁻¹)⁻¹` spelling hides the removable singularity structure.
  field_simp [hw]
  rw [one_div, neg_inv]
  ring_nf

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: away from `w = 0`, the
reciprocal outer Cauchy piece can be rewritten using the regularized kernel `(1 - w * t)⁻¹`. -/
lemma outerReciprocalPiece_eq_regularizedIntegral
    {f : ℂ → ℂ} {r : NNReal} {w : ℂ} (hw : w ≠ 0) :
    outerReciprocalPiece f r w =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ t in C(0, (r : ℝ)), (1 - w * t)⁻¹ • f t := by
  -- Unfold the reciprocal model and push the outer `w⁻¹` factor through the circle integral.
  unfold outerReciprocalPiece circleOuterPiece
  rw [smul_eq_mul]
  calc
    w⁻¹ * -((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ t in C(0, (r : ℝ)), (t - w⁻¹)⁻¹ • f t)
      = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (-(w⁻¹) * ∮ t in C(0, (r : ℝ)), (t - w⁻¹)⁻¹ • f t) := by
            ring
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ∮ t in C(0, (r : ℝ)), (-(w⁻¹) * ((t - w⁻¹)⁻¹ • f t)) := by
            rw [← circleIntegral.integral_const_mul]
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ∮ t in C(0, (r : ℝ)), (1 - w * t)⁻¹ * f t := by
            congr 1
            refine circleIntegral.integral_congr (by positivity) ?_
            intro t ht
            calc
              -(w⁻¹) * ((t - w⁻¹)⁻¹ • f t)
                  = (-(w⁻¹ * (t - w⁻¹)⁻¹)) * f t := by
                      simp [smul_eq_mul]
                      ring
              _ = (1 - w * t)⁻¹ * f t := by
                    rw [outerReciprocalKernel_eq_regularized hw]
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ t in C(0, (r : ℝ)), (1 - w * t)⁻¹ • f t := by
            simp [smul_eq_mul]

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: two inner circles inside the
annulus define the same outer Cauchy piece on the exterior of the larger circle. -/
lemma circleOuterPiece_eq_on_exterior
    {ρ₂ ρ₁ r₁ r₂ : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁))
    (hρ₂r₁ : ρ₂ < r₁) (hr₁r₂ : r₁ ≤ r₂) (hr₂ρ₁ : r₂ < ρ₁) :
    Set.EqOn (circleOuterPiece f r₁) (circleOuterPiece f r₂) ((closedBall (0 : ℂ) (r₂ : ℝ))ᶜ) := by
  intro z hz
  let closedAnnulus : Set ℂ := closedBall (0 : ℂ) (r₂ : ℝ) \ ball (0 : ℂ) (r₁ : ℝ)
  let puncturedAnnulus : Set ℂ := ball (0 : ℂ) (r₂ : ℝ) \ closedBall (0 : ℂ) (r₁ : ℝ)
  have hr₁0 : 0 < (r₁ : ℝ) := by
    exact_mod_cast lt_of_le_of_lt ρ₂.2 hρ₂r₁
  have hr₁r₂_real : (r₁ : ℝ) ≤ (r₂ : ℝ) := by
    exact_mod_cast hr₁r₂
  have hclosedAnnulus_subset : closedAnnulus ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
    -- Every point of the closed geometric annulus still satisfies the strict annulus bounds.
    intro w hw
    rcases hw with ⟨hw₂, hw₁⟩
    have hw₁' : (r₁ : ℝ) ≤ ‖w‖ := by
      have : ¬ ‖w‖ < (r₁ : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hw₁
      exact le_of_not_gt this
    have hw₂' : ‖w‖ ≤ (r₂ : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hw₂
    change (ρ₂ : ENNReal) < ‖w‖₊ ∧ ‖w‖₊ < (ρ₁ : ENNReal)
    constructor
    · exact_mod_cast lt_of_lt_of_le hρ₂r₁ hw₁'
    · exact_mod_cast lt_of_le_of_lt hw₂' hr₂ρ₁
  have hpuncturedAnnulus_subset : puncturedAnnulus ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
    -- The open geometric annulus inherits the same strict inequalities.
    intro w hw
    rcases hw with ⟨hw₂, hw₁⟩
    have hw₁' : (r₁ : ℝ) < ‖w‖ := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hw₁
    have hw₂' : ‖w‖ < (r₂ : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hw₂
    change (ρ₂ : ENNReal) < ‖w‖₊ ∧ ‖w‖₊ < (ρ₁ : ENNReal)
    constructor
    · exact_mod_cast lt_trans hρ₂r₁ hw₁'
    · exact_mod_cast lt_trans hw₂' hr₂ρ₁
  have hz_not_closedBall : z ∉ closedBall (0 : ℂ) (r₂ : ℝ) := by
    simpa [Set.mem_compl_iff] using hz
  have hkernel_cont :
      ContinuousOn (fun w : ℂ ↦ (w - z)⁻¹) closedAnnulus := by
    exact
      ((continuousOn_id.sub continuousOn_const).inv₀ fun w hw ↦
        sub_ne_zero.2 <| by
          intro hwz
          subst hwz
          exact hz_not_closedBall hw.1)
  have hintegrand_cont :
      ContinuousOn (fun w : ℂ ↦ (w - z)⁻¹ • f w) closedAnnulus :=
    hkernel_cont.smul (hf.continuousOn.mono hclosedAnnulus_subset)
  have hintegrand_diff :
      ∀ w ∈ puncturedAnnulus \ (∅ : Set ℂ), DifferentiableAt ℂ (fun u : ℂ ↦ (u - z)⁻¹ • f u) w := by
    intro w hw
    have hw_ne : w ≠ z := by
      intro hwz
      subst hwz
      exact hz_not_closedBall (ball_subset_closedBall hw.1.1)
    -- The kernel has no pole on the open annulus, so the whole integrand is holomorphic there.
    have hkernel_diff : DifferentiableAt ℂ (fun u : ℂ ↦ (u - z)⁻¹) w :=
      (differentiableAt_id.sub (differentiableAt_const z)).inv (sub_ne_zero.2 hw_ne)
    have hf_diff : DifferentiableAt ℂ f w :=
      (hf w (hpuncturedAnnulus_subset hw.1)).differentiableAt
    simpa [smul_eq_mul] using hkernel_diff.mul hf_diff
  have hintegral :
      ∮ w in C(0, (r₂ : ℝ)), (w - z)⁻¹ • f w =
        ∮ w in C(0, (r₁ : ℝ)), (w - z)⁻¹ • f w := by
    -- Cauchy-Goursat on the annulus between the two circles removes the radius dependence.
    exact
      Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr₁0 hr₁r₂_real
        Set.countable_empty hintegrand_cont hintegrand_diff
  -- After unfolding the definition, the two outer Cauchy pieces differ only by equal circle
  -- integrals.
  unfold circleOuterPiece
  rw [← hintegral]

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: after passing to the reciprocal
variable, the outer Cauchy model is independent of the inner circle on the punctured reciprocal
ball. -/
lemma outerReciprocalPiece_eq_on_puncturedBall
    {ρ₂ ρ₁ r₁ r₂ : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁))
    (hρ₂r₁ : ρ₂ < r₁) (hr₁r₂ : r₁ ≤ r₂) (hr₂ρ₁ : r₂ < ρ₁) :
    Set.EqOn (outerReciprocalPiece f r₁) (outerReciprocalPiece f r₂)
      (ball (0 : ℂ) (((r₂⁻¹ : NNReal) : ℝ)) \ {(0 : ℂ)}) := by
  intro w hw
  have hw0 : w ≠ 0 := by
    simpa using hw.2
  have hr₂0 : 0 < r₂ := lt_of_lt_of_le (lt_of_le_of_lt ρ₂.2 hρ₂r₁) hr₁r₂
  have hw_ball : w ∈ ball (0 : ℂ) (((r₂⁻¹ : NNReal) : ℝ)) := hw.1
  have hw_norm : ‖w‖ < (((r₂⁻¹ : NNReal) : ℝ)) := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hw_ball
  have hw_inv_exterior : w⁻¹ ∈ (closedBall (0 : ℂ) (r₂ : ℝ))ᶜ := by
    rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero]
    intro hw_inv_le
    have hr₂pos : 0 < (r₂ : ℝ) := by
      exact_mod_cast hr₂0
    have hmul_lt : ‖w‖ * (r₂ : ℝ) < 1 := by
      have hr₂ne : (r₂ : ℝ) ≠ 0 := ne_of_gt hr₂pos
      have hinv_mul : (((r₂⁻¹ : NNReal) : ℝ)) * (r₂ : ℝ) = 1 := by
        simpa [NNReal.coe_inv] using (inv_mul_cancel₀ hr₂ne : (r₂ : ℝ)⁻¹ * (r₂ : ℝ) = 1)
      calc
        ‖w‖ * (r₂ : ℝ) < (((r₂⁻¹ : NNReal) : ℝ)) * (r₂ : ℝ) := by
          gcongr
        _ = 1 := hinv_mul
    have hmul_eq_one : ‖w‖ * ‖w⁻¹‖ = 1 := by
      rw [← norm_mul, mul_inv_cancel₀ hw0, norm_one]
    have hmul_le : ‖w‖ * ‖w⁻¹‖ ≤ ‖w‖ * (r₂ : ℝ) :=
      mul_le_mul_of_nonneg_left hw_inv_le (norm_nonneg _)
    have : (1 : ℝ) < 1 := by
      calc
        (1 : ℝ) = ‖w‖ * ‖w⁻¹‖ := hmul_eq_one.symm
        _ ≤ ‖w‖ * (r₂ : ℝ) := hmul_le
        _ < 1 := hmul_lt
    exact (lt_irrefl (1 : ℝ)) this
  have hout :
      circleOuterPiece f r₁ (w⁻¹) = circleOuterPiece f r₂ (w⁻¹) :=
    circleOuterPiece_eq_on_exterior (f := f) (ρ₂ := ρ₂) (ρ₁ := ρ₁)
      hf hρ₂r₁ hr₁r₂ hr₂ρ₁ hw_inv_exterior
  -- Multiplying by the common outer `w⁻¹` factor preserves the reciprocal-model equality.
  simpa [outerReciprocalPiece] using congrArg (fun c : ℂ ↦ w⁻¹ * c) hout

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: on the reciprocal-radius
circle, the pulled-back boundary data for the negative Laurent branch are continuous. -/
lemma reciprocalBoundaryContinuousOnSphere
    {ρ₂ ρ₁ r : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁))
    (hρ₂r : ρ₂ < r) (hrρ₁ : r < ρ₁) :
    ContinuousOn (fun u : ℂ ↦ -(u⁻¹) * f (u⁻¹))
      (sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ))) := by
  have hsphere_inv :
      Set.MapsTo (fun u : ℂ ↦ u⁻¹) (sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ)))
        (sphere (0 : ℂ) (r : ℝ)) := by
    intro u hu
    exact inv_mem_sphere_of_mem_reciprocal_sphere (r := r) hu
  have hsphere_annulus :
      Set.MapsTo (fun u : ℂ ↦ u⁻¹) (sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ)))
        (complexOpenAnnulus ρ₂ ρ₁) := by
    intro u hu
    exact sphere_subset_complexOpenAnnulus_of_lt_lt (R := r) hρ₂r hrρ₁ (hsphere_inv hu)
  have hrinv0 : 0 < (r⁻¹ : NNReal) := by
    exact inv_pos.mpr (lt_of_le_of_lt ρ₂.2 hρ₂r)
  have hrinv0_real : 0 < (((r⁻¹ : NNReal) : ℝ)) := by
    exact_mod_cast hrinv0
  have hcont_inv :
      ContinuousOn (fun u : ℂ ↦ u⁻¹) (sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ))) := by
    refine continuousOn_inv₀.mono ?_
    intro u hu hu0
    subst hu0
    have : (0 : ℝ) = (((r⁻¹ : NNReal) : ℝ)) := by
      simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hu
    exact hrinv0_real.ne' this.symm
  have hcont_f_inv :
      ContinuousOn (fun u : ℂ ↦ f (u⁻¹)) (sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ))) := by
    exact (hf.continuousOn.comp hcont_inv hsphere_annulus)
  -- The pulled-back boundary function is a product of the reciprocal map and the composed
  -- boundary values of `f`.
  exact hcont_inv.neg.mul hcont_f_inv

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: the reciprocal boundary data
used for the negative Laurent branch are circle integrable. -/
lemma reciprocalBoundaryCircleIntegrable
    {ρ₂ ρ₁ r : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁))
    (hρ₂r : ρ₂ < r) (hrρ₁ : r < ρ₁) :
    CircleIntegrable (fun u : ℂ ↦ -(u⁻¹) * f (u⁻¹)) 0 (((r⁻¹ : NNReal) : ℝ)) := by
  -- Circle integrability is immediate from continuity on the reciprocal circle.
  exact (reciprocalBoundaryContinuousOnSphere (f := f) hf hρ₂r hrρ₁).circleIntegrable (r⁻¹).2

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: the reciprocal-circle Cauchy
model for the negative Laurent branch is analytic on the full reciprocal disc. -/
lemma reciprocalCircleInnerPiece_analyticOnNhd
    {ρ₂ ρ₁ r : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁))
    (hρ₂r : ρ₂ < r) (hrρ₁ : r < ρ₁) :
    AnalyticOnNhd ℂ
      (circleInnerPiece (fun u : ℂ ↦ -(u⁻¹) * f (u⁻¹)) (r⁻¹))
      (ball (0 : ℂ) (r⁻¹ : NNReal)) := by
  have hcircle :
      CircleIntegrable (fun u : ℂ ↦ -(u⁻¹) * f (u⁻¹)) 0 (((r⁻¹ : NNReal) : ℝ)) :=
    reciprocalBoundaryCircleIntegrable (f := f) hf hρ₂r hrρ₁
  have hrinv0 : 0 < (r⁻¹ : NNReal) := by
    exact inv_pos.mpr (lt_of_le_of_lt ρ₂.2 hρ₂r)
  -- Once the reciprocal boundary function is circle integrable, the standard Cauchy-integral
  -- power-series theorem gives analyticity on the whole reciprocal disc.
  convert
      (hasFPowerSeriesOn_cauchy_integral (c := (0 : ℂ)) (R := r⁻¹) hcircle hrinv0).analyticOnNhd
    using 1
  ext z
  simp

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: uniform convergence of a
function series on a circle allows termwise circle integration. -/
lemma circleIntegral_tsum_of_summableUniformlyOn_sphere
    {F : ℤ → ℂ → ℂ} {R : NNReal}
    (hcont : ∀ m, ContinuousOn (F m) (sphere (0 : ℂ) (R : ℝ)))
    (hsum : SummableUniformlyOn F (sphere (0 : ℂ) (R : ℝ))) :
    (∮ z in C(0, (R : ℝ)), ∑' m : ℤ, F m z) = ∑' m : ℤ, ∮ z in C(0, (R : ℝ)), F m z := by
  have hhas : HasSumUniformlyOn F (fun z ↦ ∑' m : ℤ, F m z) (sphere (0 : ℂ) (R : ℝ)) :=
    hsum.hasSumUniformlyOn
  have hcont_partial :
      ∀ s : Finset ℤ, ContinuousOn (fun z : ℂ ↦ ∑ m ∈ s, F m z) (sphere (0 : ℂ) (R : ℝ)) := by
    -- Finite partial sums preserve continuity on the circle.
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (0 : ℂ)) _)
    · intro m s hm hs
      simpa [Finset.sum_insert, hm] using (hcont m).add hs
  have htendsto :
      Filter.Tendsto (fun s : Finset ℤ ↦ ∮ z in C(0, (R : ℝ)), ∑ m ∈ s, F m z) Filter.atTop
        (𝓝 (∮ z in C(0, (R : ℝ)), ∑' m : ℤ, F m z)) :=
    hhas.tendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn R.2
      (Filter.Eventually.of_forall hcont_partial)
  have hsum_int :
      HasSum (fun m : ℤ ↦ ∮ z in C(0, (R : ℝ)), F m z)
        (∮ z in C(0, (R : ℝ)), ∑' m : ℤ, F m z) := by
    rw [HasSum]
    convert htendsto using 1
    ext s
    symm
    exact circleIntegral.integral_fun_sum fun m _ ↦ (hcont m).circleIntegrable R.2
  exact hsum_int.tsum_eq.symm

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: a uniformly summable
natural-indexed series on a circle may be integrated termwise. -/
lemma circleIntegral_tsum_of_summableUniformlyOn_sphere_nat
    {F : ℕ → ℂ → ℂ} {R : NNReal}
    (hcont : ∀ n, ContinuousOn (F n) (sphere (0 : ℂ) (R : ℝ)))
    (hsum : SummableUniformlyOn F (sphere (0 : ℂ) (R : ℝ))) :
    (∮ z in C(0, (R : ℝ)), ∑' n : ℕ, F n z) = ∑' n : ℕ, ∮ z in C(0, (R : ℝ)), F n z := by
  have hhas : HasSumUniformlyOn F (fun z ↦ ∑' n : ℕ, F n z) (sphere (0 : ℂ) (R : ℝ)) :=
    hsum.hasSumUniformlyOn
  have hcont_partial :
      ∀ s : Finset ℕ, ContinuousOn (fun z : ℂ ↦ ∑ n ∈ s, F n z) (sphere (0 : ℂ) (R : ℝ)) := by
    -- Finite partial sums preserve continuity on the circle.
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (0 : ℂ)) _)
    · intro n s hn hs
      simpa [Finset.sum_insert, hn] using (hcont n).add hs
  have htendsto :
      Filter.Tendsto (fun s : Finset ℕ ↦ ∮ z in C(0, (R : ℝ)), ∑ n ∈ s, F n z) Filter.atTop
        (𝓝 (∮ z in C(0, (R : ℝ)), ∑' n : ℕ, F n z)) :=
    hhas.tendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn R.2
      (Filter.Eventually.of_forall hcont_partial)
  have hsum_int :
      HasSum (fun n : ℕ ↦ ∮ z in C(0, (R : ℝ)), F n z)
        (∮ z in C(0, (R : ℝ)), ∑' n : ℕ, F n z) := by
    rw [HasSum]
    convert htendsto using 1
    ext s
    symm
    exact circleIntegral.integral_fun_sum fun n _ ↦ (hcont n).circleIntegrable R.2
  exact hsum_int.tsum_eq.symm

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: uniform convergence of the
nonnegative and negative tails on the same set combines to uniform convergence of the full
integer-indexed Laurent family. -/
lemma summableUniformlyOn_intRec
    {s : Set ℂ} {f g : ℕ → ℂ → ℂ}
    (hf : SummableUniformlyOn f s) (hg : SummableUniformlyOn g s) :
    SummableUniformlyOn (fun m : ℤ ↦ Int.rec f g m) s := by
  -- Unfold uniform summability to summability in `UniformOnFun`, then combine the two tails with
  -- the standard `Int.rec` summation constructor.
  change Summable (fun m : ℤ ↦ UniformOnFun.ofFun {s} (Int.rec f g m))
  simpa [Function.comp_def] using
    (Summable.int_rec
      (show Summable (fun n : ℕ ↦ UniformOnFun.ofFun {s} (f n)) by
        simpa [SummableUniformlyOn, Function.comp_def] using hf)
      (show Summable (fun n : ℕ ↦ UniformOnFun.ofFun {s} (g n)) by
        simpa [SummableUniformlyOn, Function.comp_def] using hg))

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: the nonnegative Laurent
coefficient obtained by integrating on the radius-`R` circle. -/
noncomputable def posLaurentCoeff (f : ℂ → ℂ) (R : NNReal) (n : ℕ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ t in C(0, (R : ℝ)), (t ^ (Int.negSucc n)) * f t

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: the negative Laurent
coefficient obtained by integrating on the radius-`r` circle. -/
noncomputable def negLaurentCoeff (f : ℂ → ℂ) (r : NNReal) (n : ℕ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ t in C(0, (r : ℝ)), (t ^ n) * f t

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: the positive Laurent
coefficient integrals are independent of the chosen outer radius. -/
lemma posCoeff_radiusInvariant
    {ρ₂ ρ₁ R₁ R₂ : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁))
    (hρ₂R₁ : ρ₂ < R₁) (hR₁R₂ : R₁ ≤ R₂) (hR₂ρ₁ : R₂ < ρ₁) (n : ℕ) :
    posLaurentCoeff f R₁ n = posLaurentCoeff f R₂ n := by
  let closedAnnulus : Set ℂ := closedBall (0 : ℂ) (R₂ : ℝ) \ ball (0 : ℂ) (R₁ : ℝ)
  let puncturedAnnulus : Set ℂ := ball (0 : ℂ) (R₂ : ℝ) \ closedBall (0 : ℂ) (R₁ : ℝ)
  have hR₁0 : 0 < (R₁ : ℝ) := by
    exact_mod_cast lt_of_le_of_lt ρ₂.2 hρ₂R₁
  have hR₁R₂_real : (R₁ : ℝ) ≤ (R₂ : ℝ) := by
    exact_mod_cast hR₁R₂
  have hclosedAnnulus_subset : closedAnnulus ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
    -- Every point of the geometric annulus keeps the same strict annulus bounds.
    intro w hw
    rcases hw with ⟨hw₂, hw₁⟩
    have hw₁' : (R₁ : ℝ) ≤ ‖w‖ := by
      have : ¬ ‖w‖ < (R₁ : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hw₁
      exact le_of_not_gt this
    have hw₂' : ‖w‖ ≤ (R₂ : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hw₂
    change (ρ₂ : ENNReal) < ‖w‖₊ ∧ ‖w‖₊ < (ρ₁ : ENNReal)
    constructor
    · exact_mod_cast lt_of_lt_of_le hρ₂R₁ hw₁'
    · exact_mod_cast lt_of_le_of_lt hw₂' hR₂ρ₁
  have hpuncturedAnnulus_subset : puncturedAnnulus ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
    -- The open annulus also inherits the same strict inequalities.
    intro w hw
    rcases hw with ⟨hw₂, hw₁⟩
    have hw₁' : (R₁ : ℝ) < ‖w‖ := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hw₁
    have hw₂' : ‖w‖ < (R₂ : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hw₂
    change (ρ₂ : ENNReal) < ‖w‖₊ ∧ ‖w‖₊ < (ρ₁ : ENNReal)
    constructor
    · exact_mod_cast lt_trans hρ₂R₁ hw₁'
    · exact_mod_cast lt_trans hw₂' hR₂ρ₁
  have hintegrand_cont :
      ContinuousOn (fun t : ℂ ↦ (t ^ (Int.negSucc n)) * f t) closedAnnulus := by
    -- The annulus excludes `0`, so the negative power is continuous there.
    have hpow_cont : ContinuousOn (fun t : ℂ ↦ t ^ (Int.negSucc n)) closedAnnulus := by
      refine (continuousOn_zpow₀ (Int.negSucc n)).mono ?_
      intro t ht ht0
      have hzero_ball : (0 : ℂ) ∈ ball (0 : ℂ) (R₁ : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hR₁0
      exact ht.2 (ht0 ▸ hzero_ball)
    exact hpow_cont.mul (hf.continuousOn.mono hclosedAnnulus_subset)
  have hintegrand_diff :
      ∀ w ∈ puncturedAnnulus \ (∅ : Set ℂ),
        DifferentiableAt ℂ (fun t : ℂ ↦ (t ^ (Int.negSucc n)) * f t) w := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro hw0
      have hzero_closedBall : (0 : ℂ) ∈ closedBall (0 : ℂ) (R₁ : ℝ) := by
        simp [Metric.mem_closedBall]
      exact hw.1.2 (hw0 ▸ hzero_closedBall)
    have hf_diff : DifferentiableAt ℂ f w :=
      (hf w (hpuncturedAnnulus_subset hw.1)).differentiableAt
    have hpow_diff : DifferentiableAt ℂ (fun t : ℂ ↦ t ^ (Int.negSucc n)) w :=
      DifferentiableAt.zpow differentiableAt_id (m := Int.negSucc n) (Or.inl hw0)
    simpa using hpow_diff.mul hf_diff
  -- Cauchy-Goursat on the punctured annulus removes the radius dependence of the coefficient.
  unfold posLaurentCoeff
  refine congrArg (fun s : ℂ ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ • s) ?_
  exact
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hR₁0 hR₁R₂_real
      Set.countable_empty hintegrand_cont hintegrand_diff |>.symm


/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: the inner-circle coefficient
integrals defining the negative Laurent tail are independent of the chosen radius. -/
lemma negCoeff_radiusInvariant
    {ρ₂ ρ₁ r₁ r₂ : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁))
    (hρ₂r₁ : ρ₂ < r₁) (hr₁r₂ : r₁ ≤ r₂) (hr₂ρ₁ : r₂ < ρ₁) (n : ℕ) :
    (∮ t in C(0, (r₁ : ℝ)), (t ^ n) * f t) = ∮ t in C(0, (r₂ : ℝ)), (t ^ n) * f t := by
  let closedAnnulus : Set ℂ := closedBall (0 : ℂ) (r₂ : ℝ) \ ball (0 : ℂ) (r₁ : ℝ)
  let puncturedAnnulus : Set ℂ := ball (0 : ℂ) (r₂ : ℝ) \ closedBall (0 : ℂ) (r₁ : ℝ)
  have hr₁0 : 0 < (r₁ : ℝ) := by
    exact_mod_cast lt_of_le_of_lt ρ₂.2 hρ₂r₁
  have hr₁r₂_real : (r₁ : ℝ) ≤ (r₂ : ℝ) := by
    exact_mod_cast hr₁r₂
  have hclosedAnnulus_subset : closedAnnulus ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
    -- Every point of the closed geometric annulus still satisfies the strict annulus bounds.
    intro w hw
    rcases hw with ⟨hw₂, hw₁⟩
    have hw₁' : (r₁ : ℝ) ≤ ‖w‖ := by
      have : ¬ ‖w‖ < (r₁ : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hw₁
      exact le_of_not_gt this
    have hw₂' : ‖w‖ ≤ (r₂ : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hw₂
    change (ρ₂ : ENNReal) < ‖w‖₊ ∧ ‖w‖₊ < (ρ₁ : ENNReal)
    constructor
    · exact_mod_cast lt_of_lt_of_le hρ₂r₁ hw₁'
    · exact_mod_cast lt_of_le_of_lt hw₂' hr₂ρ₁
  have hpuncturedAnnulus_subset : puncturedAnnulus ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
    -- The open geometric annulus inherits the same strict inequalities.
    intro w hw
    rcases hw with ⟨hw₂, hw₁⟩
    have hw₁' : (r₁ : ℝ) < ‖w‖ := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hw₁
    have hw₂' : ‖w‖ < (r₂ : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hw₂
    change (ρ₂ : ENNReal) < ‖w‖₊ ∧ ‖w‖₊ < (ρ₁ : ENNReal)
    constructor
    · exact_mod_cast lt_trans hρ₂r₁ hw₁'
    · exact_mod_cast lt_trans hw₂' hr₂ρ₁
  have hintegrand_cont :
      ContinuousOn (fun t : ℂ ↦ (t ^ n) * f t) closedAnnulus :=
    ((continuousOn_id.pow n).mul (hf.continuousOn.mono hclosedAnnulus_subset))
  have hintegrand_diff :
      ∀ w ∈ puncturedAnnulus \ (∅ : Set ℂ),
        DifferentiableAt ℂ (fun t : ℂ ↦ (t ^ n) * f t) w := by
    intro w hw
    have hf_diff : DifferentiableAt ℂ f w :=
      (hf w (hpuncturedAnnulus_subset hw.1)).differentiableAt
    simpa using (differentiableAt_id.pow n).mul hf_diff
  -- The polynomially weighted boundary integrals are equal by Cauchy-Goursat on the annulus.
  exact
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr₁0 hr₁r₂_real
      Set.countable_empty hintegrand_cont hintegrand_diff |>.symm

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: the negative Laurent
coefficients are independent of the chosen inner contour. -/
lemma negLaurentCoeff_radiusInvariant
    {ρ₂ ρ₁ r₁ r₂ : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁))
    (hρ₂r₁ : ρ₂ < r₁) (hr₁r₂ : r₁ ≤ r₂) (hr₂ρ₁ : r₂ < ρ₁) (n : ℕ) :
    negLaurentCoeff f r₁ n = negLaurentCoeff f r₂ n := by
  -- This is the coefficient-level wrapper used by the final Laurent family.
  unfold negLaurentCoeff
  refine congrArg (fun s : ℂ ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ • s) ?_
  exact negCoeff_radiusInvariant hf hρ₂r₁ hr₁r₂ hr₂ρ₁ n

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: every point of the smaller
disc admits an intermediate outer circle that still lies inside the annulus. -/
lemma exists_intermediate_radius_for_ball_point
    {ρ₂ ρ₁ : NNReal} (hρ : ρ₂ < ρ₁) {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ₁) :
    ∃ R : NNReal, max ρ₂ ‖z‖₊ < R ∧ R < ρ₁ := by
  -- The point lies strictly inside the outer radius, so there is room to choose an intermediate
  -- contour radius strictly between `max ρ₂ ‖z‖` and `ρ₁`.
  have hzlt : ‖z‖₊ < ρ₁ := by
    exact_mod_cast
      (by simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hz : ‖z‖ < (ρ₁ : ℝ))
  have hmax : max ρ₂ ‖z‖₊ < ρ₁ := max_lt_iff.mpr ⟨hρ, hzlt⟩
  exact exists_between hmax

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: every point of the exterior of
the closed ball admits an intermediate inner radius strictly between `ρ₂` and its norm. -/
lemma exists_intermediate_radius_for_exterior_point
    {ρ₂ : NNReal} {z : ℂ} (hz : z ∈ (closedBall (0 : ℂ) ρ₂)ᶜ) :
    ∃ r : NNReal, ρ₂ < r ∧ r < ‖z‖₊ := by
  -- The exterior condition is exactly the strict inequality `ρ₂ < ‖z‖`.
  have hzgt : ρ₂ < ‖z‖₊ := by
    have hznot : ¬ ‖z‖ ≤ (ρ₂ : ℝ) := by
      simpa [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
    exact_mod_cast lt_of_not_ge hznot
  exact exists_between hzgt

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: for a point outside the closed
inner ball one can choose an intermediate inner circle that also stays below the outer radius. -/
lemma exists_intermediate_radius_for_exterior_point_lt_upper
    {ρ₂ ρ₁ : NNReal} (hρ : ρ₂ < ρ₁) {z : ℂ} (hz : z ∈ (closedBall (0 : ℂ) ρ₂)ᶜ) :
    ∃ r : NNReal, ρ₂ < r ∧ r < ρ₁ ∧ r < ‖z‖₊ := by
  -- We choose `r` between `ρ₂` and the smaller of `ρ₁` and `‖z‖`, so the reciprocal circle
  -- remains inside the original annulus.
  have hzgt : ρ₂ < ‖z‖₊ := by
    rcases exists_intermediate_radius_for_exterior_point (ρ₂ := ρ₂) hz with ⟨r, hρ₂r, hrz⟩
    exact lt_trans hρ₂r hrz
  rcases exists_between (lt_min hρ hzgt) with ⟨r, hρ₂r, hrmin⟩
  exact
    ⟨r, hρ₂r, lt_of_lt_of_le hrmin (min_le_left _ _), lt_of_lt_of_le hrmin (min_le_right _ _)⟩

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: the outer Cauchy branch on the
radius-`R` circle has the positive Laurent coefficients as its scalar power-series data. -/
lemma circleInnerPiece_hasFPowerSeries_posCoeff
    {ρ₂ ρ₁ R : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁))
    (hρ₂ : ρ₂ < R) (hρ₁ : R < ρ₁) :
    HasFPowerSeriesOnBall (circleInnerPiece f R)
      (FormalMultilinearSeries.ofScalars ℂ (posLaurentCoeff f R)) 0 R := by
  have hsphere :
      sphere (0 : ℂ) (R : ℝ) ⊆ complexOpenAnnulus ρ₂ ρ₁ :=
    sphere_subset_complexOpenAnnulus_of_lt_lt hρ₂ hρ₁
  have hcont : ContinuousOn f (sphere (0 : ℂ) (R : ℝ)) :=
    hf.continuousOn.mono hsphere
  have hcircle : CircleIntegrable f 0 (R : ℝ) :=
    hcont.circleIntegrable R.2
  have hR0 : 0 < R := lt_of_le_of_lt ρ₂.2 hρ₂
  have hbase :
      HasFPowerSeriesOnBall (circleInnerPiece f R) (cauchyPowerSeries f 0 (R : ℝ)) 0 R := by
    -- The standard Cauchy-integral power-series theorem already packages the positive branch.
    convert (hasFPowerSeriesOn_cauchy_integral (c := (0 : ℂ)) (R := R) hcircle hR0) using 1
  have hseries :
      cauchyPowerSeries f 0 (R : ℝ) =
        FormalMultilinearSeries.ofScalars ℂ (posLaurentCoeff f R) := by
    -- The `n`th Cauchy coefficient is exactly the circle integral defining `posLaurentCoeff`.
    ext n
    rw [← FormalMultilinearSeries.mkPiRing_coeff_eq
        (p := cauchyPowerSeries f 0 (R : ℝ))]
    rw [← FormalMultilinearSeries.mkPiRing_coeff_eq
        (p := FormalMultilinearSeries.ofScalars ℂ (posLaurentCoeff f R))]
    rw [FormalMultilinearSeries.coeff_ofScalars]
    have hcoeff :
        (cauchyPowerSeries f 0 (R : ℝ)).coeff n = posLaurentCoeff f R n := by
      change cauchyPowerSeries f 0 (R : ℝ) n (fun _ ↦ (1 : ℂ)) = posLaurentCoeff f R n
      rw [cauchyPowerSeries_apply]
      -- On the positive-radius circle, the Cauchy kernel simplifies to the expected negative power.
      unfold posLaurentCoeff
      refine congrArg (fun s : ℂ ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ • s) ?_
      refine circleIntegral.integral_congr R.2 ?_
      intro z hz
      have hz0 : z ≠ 0 := by
        have hzR : ‖z‖ = (R : ℝ) := by
          simpa using mem_sphere_iff_norm.mp hz
        exact fun hz0 ↦ (ne_of_gt (show (0 : ℝ) < R by exact_mod_cast hR0)) <|
          by simpa [hz0] using hzR.symm
      calc
        (1 / (z - 0)) ^ n • (z - 0)⁻¹ • f z = (((1 / z : ℂ) ^ n) * z⁻¹) * f z := by
          simp [sub_zero, smul_eq_mul, mul_assoc]
        _ = z ^ (Int.negSucc n) * f z := by
          congr 1
          calc
            ((1 / z : ℂ) ^ n) * z⁻¹ = (z ^ n)⁻¹ * z⁻¹ := by simp [one_div]
            _ = z⁻¹ * (z ^ n)⁻¹ := by ac_rfl
            _ = (z ^ n * z)⁻¹ := by rw [mul_inv_rev]
            _ = ((z ^ (n + 1 : ℕ)) : ℂ)⁻¹ := by rw [pow_succ]
            _ = z ^ (Int.negSucc n) := by rw [zpow_negSucc]
    exact congrArg
      (fun q : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ ℂ) ℂ ↦ q (fun _ ↦ (1 : ℂ)))
      (congrArg (ContinuousMultilinearMap.mkPiRing ℂ (Fin n)) hcoeff)
  simpa [hseries] using hbase

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: on any smaller ball, the outer
Cauchy branch equals the positive Laurent power series determined by the same contour. -/
lemma circleInnerPiece_eq_posPowerSeriesOnBall
    {ρ₂ ρ₁ R : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁))
    (hρ₂ : ρ₂ < R) (hρ₁ : R < ρ₁) :
    Set.EqOn (circleInnerPiece f R)
      (fun z : ℂ ↦ ∑' n : ℕ, posLaurentCoeff f R n * z ^ n)
      (ball (0 : ℂ) (R : ℝ)) := by
  have hpower :
      HasFPowerSeriesOnBall (circleInnerPiece f R)
        (FormalMultilinearSeries.ofScalars ℂ (posLaurentCoeff f R)) 0 R :=
    circleInnerPiece_hasFPowerSeries_posCoeff (f := f) hf hρ₂ hρ₁
  intro z hz
  have hzeball : z ∈ Metric.eball (0 : ℂ) R := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub, sub_zero] using hz
  have hsum :
      HasSum (fun n : ℕ ↦ posLaurentCoeff f R n * z ^ n) (circleInnerPiece f R z) := by
    -- Evaluating the formal scalar power series at `z` recovers the usual power series sum.
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hpower.hasSum_sub hzeball
  exact hsum.tsum_eq.symm

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: on the exterior of the
radius-`r` circle, the inner Cauchy contour equals the negative Laurent tail determined by that
circle. -/
lemma circleOuterPiece_eq_negLaurentTailOnExterior
    {ρ₂ ρ₁ r : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁))
    (hρ₂r : ρ₂ < r) (hrρ₁ : r < ρ₁) :
    Set.EqOn (circleOuterPiece f r)
      (fun z : ℂ ↦ ∑' n : ℕ, negLaurentCoeff f r n * z ^ (Int.negSucc n))
      ((closedBall (0 : ℂ) (r : ℝ))ᶜ) := by
  intro z hz
  have hr0 : 0 < r := lt_of_le_of_lt ρ₂.2 hρ₂r
  have hr0_real : 0 < (r : ℝ) := by
    exact_mod_cast hr0
  have hz_norm : r < ‖z‖₊ := by
    have hznot : ¬ ‖z‖ ≤ (r : ℝ) := by
      simpa [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
    exact_mod_cast lt_of_not_ge hznot
  have hz0 : z ≠ 0 := by
    intro hz0
    have : (r : ℝ) < 0 := by
      simpa [hz0] using (show (r : ℝ) < ‖z‖ by exact_mod_cast hz_norm)
    exact (not_lt_of_ge hr0_real.le) this
  let w : ℂ := z⁻¹
  have hw0 : w ≠ 0 := inv_ne_zero hz0
  have hwball : w ∈ ball (0 : ℂ) (((r⁻¹ : NNReal) : ℝ)) :=
    inv_mem_ball_zero_inv_radius_of_lt hr0 hz_norm
  have hw_norm : ‖w‖ < (((r⁻¹ : NNReal) : ℝ)) := by
    simpa [w, Metric.mem_ball, dist_eq_norm, sub_zero] using hwball
  have hsphere :
      sphere (0 : ℂ) (r : ℝ) ⊆ complexOpenAnnulus ρ₂ ρ₁ :=
    sphere_subset_complexOpenAnnulus_of_lt_lt (R := r) hρ₂r hrρ₁
  have hcont : ContinuousOn f (sphere (0 : ℂ) (r : ℝ)) :=
    hf.continuousOn.mono hsphere
  obtain ⟨M, hM⟩ :=
    (isCompact_sphere (0 : ℂ) (r : ℝ)).exists_bound_of_continuousOn
      (f := fun x : ℂ ↦ ‖f x‖) hcont.norm
  let F : ℕ → ℂ → ℂ := fun n t ↦ w ^ n * (t ^ n * f t)
  have hw_ratio : ‖w‖ * (r : ℝ) < 1 := by
    have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr0_real
    have hinv_mul : (((r⁻¹ : NNReal) : ℝ)) * (r : ℝ) = 1 := by
      simpa [NNReal.coe_inv] using (inv_mul_cancel₀ hr_ne : (r : ℝ)⁻¹ * (r : ℝ) = 1)
    calc
      ‖w‖ * (r : ℝ) < (((r⁻¹ : NNReal) : ℝ)) * (r : ℝ) := by
        gcongr
      _ = 1 := hinv_mul
  have hFcont :
      ∀ n, ContinuousOn (F n) (sphere (0 : ℂ) (r : ℝ)) := by
    -- Each shifted kernel term is a product of a constant coefficient, a polynomial monomial, and
    -- the boundary values of `f`.
    intro n
    exact (continuousOn_const.mul ((continuousOn_id.pow n).mul hcont))
  have hFsum :
      SummableUniformlyOn F (sphere (0 : ℂ) (r : ℝ)) := by
    -- The geometric factor `‖w‖ * r < 1` bounds the whole kernel series uniformly on the circle.
    refine
      (HasSumUniformlyOn.of_norm_le_summable
        (u := fun n : ℕ ↦ max M 0 * (‖w‖ * (r : ℝ)) ^ n) ?_ ?_).summableUniformlyOn
    · exact Summable.mul_left (max M 0)
        (summable_geometric_of_lt_one (by positivity) hw_ratio)
    · intro n t ht
      have ht_norm : ‖t‖ = (r : ℝ) := by
        simpa using mem_sphere_iff_norm.mp ht
      calc
        ‖F n t‖ = ‖w‖ ^ n * (‖t‖ ^ n * ‖f t‖) := by
            simp [F, norm_pow, mul_assoc, mul_left_comm, mul_comm]
        _ ≤ ‖w‖ ^ n * ((r : ℝ) ^ n * max M 0) := by
            have hMt : ‖f t‖ ≤ M := by
              simpa using hM t ht
            gcongr
            · rw [ht_norm]
            · exact le_trans hMt (le_max_left _ _)
        _ = max M 0 * (‖w‖ * (r : ℝ)) ^ n := by
            calc
              ‖w‖ ^ n * ((r : ℝ) ^ n * max M 0)
                  = ‖w‖ ^ n * (r : ℝ) ^ n * max M 0 := by ring
              _ = (‖w‖ * (r : ℝ)) ^ n * max M 0 := by rw [← mul_pow]
              _ = max M 0 * (‖w‖ * (r : ℝ)) ^ n := by ring
  have hkernel :
      (∮ t in C(0, (r : ℝ)), (1 - w * t)⁻¹ • f t) =
        ∑' n : ℕ, ∮ t in C(0, (r : ℝ)), F n t := by
    -- On the circle, the regularized kernel expands as a geometric series with ratio `w * t`.
    calc
      (∮ t in C(0, (r : ℝ)), (1 - w * t)⁻¹ • f t)
        = ∮ t in C(0, (r : ℝ)), ∑' n : ℕ, F n t := by
            refine circleIntegral.integral_congr hr0_real.le ?_
            intro t ht
            have ht_norm : ‖t‖ = (r : ℝ) := by
              simpa using mem_sphere_iff_norm.mp ht
            have hwt_lt : ‖w * t‖ < 1 := by
              simpa [norm_mul, ht_norm] using hw_ratio
            have hgeom :
                HasSum (fun n : ℕ ↦ (w * t) ^ n * f t) ((1 - w * t)⁻¹ * f t) :=
              (hasSum_geometric_of_norm_lt_one hwt_lt).mul_right (f t)
            calc
              (1 - w * t)⁻¹ • f t = ((1 - w * t)⁻¹) * f t := by
                simp [smul_eq_mul]
              _ = ∑' n : ℕ, (w * t) ^ n * f t := hgeom.tsum_eq.symm
              _ = ∑' n : ℕ, F n t := by
                refine tsum_congr ?_
                intro n
                simp [F, mul_pow, mul_assoc, mul_comm]
      _ = ∑' n : ℕ, ∮ t in C(0, (r : ℝ)), F n t := by
            exact circleIntegral_tsum_of_summableUniformlyOn_sphere_nat hFcont hFsum
  have hw_inv : w⁻¹ = z := by
    simp [w]
  have hw_mul : w * outerReciprocalPiece f r w = circleOuterPiece f r z := by
    -- Multiplying the reciprocal model by `w = z⁻¹` returns the original outer contour piece.
    calc
      w * outerReciprocalPiece f r w
          = (w * w⁻¹) * circleOuterPiece f r (w⁻¹) := by
              simp [outerReciprocalPiece, mul_assoc]
      _ = circleOuterPiece f r z := by
            rw [mul_inv_cancel₀ hw0, one_mul, hw_inv]
  calc
    circleOuterPiece f r z = w * outerReciprocalPiece f r w := by
      simpa [mul_comm] using hw_mul.symm
    _ = w * ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ t in C(0, (r : ℝ)), (1 - w * t)⁻¹ • f t) := by
            rw [outerReciprocalPiece_eq_regularizedIntegral (f := f) (r := r) hw0]
    _ = w * ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∑' n : ℕ, ∮ t in C(0, (r : ℝ)), F n t) := by
            rw [hkernel]
    _ = w * (((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∑' n : ℕ, ∮ t in C(0, (r : ℝ)), F n t) := by
            rw [smul_eq_mul]
    _ = w * (∑' n : ℕ, ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∮ t in C(0, (r : ℝ)), F n t) := by
            rw [← tsum_mul_left]
    _ = ∑' n : ℕ, w * (((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∮ t in C(0, (r : ℝ)), F n t) := by
            rw [← tsum_mul_left]
    _ = ∑' n : ℕ, negLaurentCoeff f r n * z ^ (Int.negSucc n) := by
            refine tsum_congr ?_
            intro n
            have hFn :
                (∮ t in C(0, (r : ℝ)), F n t) =
                  w ^ n * ∮ t in C(0, (r : ℝ)), (t ^ n) * f t := by
              -- Pull the constant factor `w ^ n` through the circle integral once.
              simpa [F, mul_assoc, mul_left_comm, mul_comm] using
                (circleIntegral.integral_const_mul
                  (f := fun t : ℂ ↦ (t ^ n) * f t) (a := w ^ n) (c := (0 : ℂ)) (R := (r : ℝ)))
            calc
              w * ((2 * Real.pi * Complex.I : ℂ)⁻¹ * ∮ t in C(0, (r : ℝ)), F n t)
                  = w * ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
                      (w ^ n * ∮ t in C(0, (r : ℝ)), (t ^ n) * f t)) := by
                        rw [hFn]
              _ = (((2 * Real.pi * Complex.I : ℂ)⁻¹ *
                    ∮ t in C(0, (r : ℝ)), (t ^ n) * f t) * (w * w ^ n)) := by
                      ring
              _ = (((2 * Real.pi * Complex.I : ℂ)⁻¹ *
                    ∮ t in C(0, (r : ℝ)), (t ^ n) * f t) * z ^ (Int.negSucc n)) := by
                      congr 1
                      calc
                        w * w ^ n = z⁻¹ * (z⁻¹) ^ n := by simp [w]
                        _ = z⁻¹ * (z ^ n)⁻¹ := by rw [inv_pow]
                        _ = ((z ^ n) * z)⁻¹ := by rw [mul_inv_rev]
                        _ = ((z ^ (n + 1 : ℕ)) : ℂ)⁻¹ := by rw [pow_succ]
                        _ = z ^ (Int.negSucc n) := by rw [zpow_negSucc]
              _ = negLaurentCoeff f r n * z ^ (Int.negSucc n) := by
                      simp [negLaurentCoeff, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: Cauchy's estimate on a circle
bounds the nonnegative Laurent coefficients attached to that circle. -/
lemma normPosLaurentCoeff_le_circleBound
    {f : ℂ → ℂ} {R : NNReal} (hR : 0 < R) {M : ℝ}
    (hM : ∀ z ∈ sphere (0 : ℂ) (R : ℝ), ‖f z‖ ≤ M) (n : ℕ) :
    ‖posLaurentCoeff f R n‖ ≤ M / (R : ℝ) ^ n := by
  have hintegrand_bound :
      ∀ z ∈ sphere (0 : ℂ) (R : ℝ),
        ‖(z ^ (Int.negSucc n)) * f z‖ ≤ M / (R : ℝ) ^ (n + 1) := by
    -- On the circle `|z| = R`, the kernel contributes the exact factor `R^(-(n+1))`.
    intro z hz
    have hz_norm : ‖z‖ = (R : ℝ) := by
      simpa using mem_sphere_iff_norm.mp hz
    calc
      ‖(z ^ (Int.negSucc n)) * f z‖ = ‖z ^ (Int.negSucc n)‖ * ‖f z‖ := by
        rw [norm_mul]
      _ = ((R : ℝ) ^ (n + 1))⁻¹ * ‖f z‖ := by
        rw [norm_zpow, hz_norm, zpow_negSucc]
      _ ≤ ((R : ℝ) ^ (n + 1))⁻¹ * M := by
        gcongr
        exact hM z hz
      _ = M / (R : ℝ) ^ (n + 1) := by
        rw [div_eq_mul_inv, mul_comm]
  have hbound :=
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      (f := fun z : ℂ ↦ (z ^ (Int.negSucc n)) * f z) hR.le hintegrand_bound
  calc
    ‖posLaurentCoeff f R n‖
        ≤ (R : ℝ) * (M / (R : ℝ) ^ (n + 1)) := hbound
    _ = M / (R : ℝ) ^ n := by
      field_simp [pow_succ]
      ring

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: Cauchy's estimate on a circle
bounds the negative Laurent coefficients attached to that circle. -/
lemma normNegLaurentCoeff_le_circleBound
    {f : ℂ → ℂ} {r : NNReal} (hr : 0 < r) {M : ℝ}
    (hM : ∀ z ∈ sphere (0 : ℂ) (r : ℝ), ‖f z‖ ≤ M) (n : ℕ) :
    ‖negLaurentCoeff f r n‖ ≤ M * (r : ℝ) ^ (n + 1) := by
  have hintegrand_bound :
      ∀ z ∈ sphere (0 : ℂ) (r : ℝ),
        ‖(z ^ n) * f z‖ ≤ (r : ℝ) ^ n * M := by
    -- On the inner circle, the polynomial weight contributes the exact factor `r^n`.
    intro z hz
    have hz_norm : ‖z‖ = (r : ℝ) := by
      simpa using mem_sphere_iff_norm.mp hz
    calc
      ‖(z ^ n) * f z‖ = ‖z ^ n‖ * ‖f z‖ := by rw [norm_mul]
      _ = (r : ℝ) ^ n * ‖f z‖ := by rw [norm_pow, hz_norm]
      _ ≤ (r : ℝ) ^ n * M := by
        gcongr
        exact hM z hz
  have hbound :=
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      (f := fun z : ℂ ↦ (z ^ n) * f z) hr.le hintegrand_bound
  calc
    ‖negLaurentCoeff f r n‖ ≤ (r : ℝ) * ((r : ℝ) ^ n * M) := hbound
    _ = M * (r : ℝ) ^ (n + 1) := by
      ring_nf

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: once the reference radii and
one smaller closed subannulus are fixed inside a finite ambient annulus, the reference Laurent
family is uniformly summable on that closed subannulus. -/
lemma referenceLaurentFamily_summableUniformlyOn_closedSubannulus
    {ρL ρU r rRef rMid RMid RRef R : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρL ρU))
    (hρLr : ρL < r) (hrrRef : r < rRef) (hrRefRRef : rRef < RRef)
    (hRRefR : RRef < R) (hRρU : R < ρU)
    (hrrMid : r < rMid) (hrMidRMid : rMid ≤ RMid) (hRMidR : RMid < R) :
    SummableUniformlyOn
      (laurentTerm (fun m : ℤ ↦ Int.rec (posLaurentCoeff f RRef) (negLaurentCoeff f rRef) m))
      (complexClosedAnnulus rMid RMid) := by
  let a : ℤ → ℂ := fun m ↦ Int.rec (posLaurentCoeff f RRef) (negLaurentCoeff f rRef) m
  let s : Set ℂ := complexClosedAnnulus rMid RMid
  let posTerm : ℕ → ℂ → ℂ := fun n z ↦ posLaurentCoeff f RRef n * z ^ n
  let negTerm : ℕ → ℂ → ℂ := fun n z ↦ negLaurentCoeff f rRef n * z ^ (Int.negSucc n)
  have hr0 : 0 < r := lt_of_le_of_lt ρL.2 hρLr
  have hrMid0 : 0 < rMid := lt_trans hr0 hrrMid
  have hrR : r < R := lt_trans hrrMid (lt_of_le_of_lt hrMidRMid hRMidR)
  have hρLR : ρL < R := lt_trans hρLr hrR
  have hR0 : 0 < R := lt_trans hr0 hrR
  have hrρU : r < ρU := lt_trans hrR hRρU
  have hRRefρU : RRef < ρU := lt_trans hRRefR hRρU
  have hsphereR :
      sphere (0 : ℂ) (R : ℝ) ⊆ complexOpenAnnulus ρL ρU :=
    sphere_subset_complexOpenAnnulus_of_lt_lt (R := R) hρLR hRρU
  have hspherer :
      sphere (0 : ℂ) (r : ℝ) ⊆ complexOpenAnnulus ρL ρU :=
    sphere_subset_complexOpenAnnulus_of_lt_lt (R := r) hρLr hrρU
  have hcontR : ContinuousOn f (sphere (0 : ℂ) (R : ℝ)) :=
    hf.continuousOn.mono hsphereR
  have hcontr : ContinuousOn f (sphere (0 : ℂ) (r : ℝ)) :=
    hf.continuousOn.mono hspherer
  obtain ⟨MR0, hMR0⟩ := (isCompact_sphere (0 : ℂ) (R : ℝ)).exists_bound_of_continuousOn hcontR
  obtain ⟨Mr0, hMr0⟩ := (isCompact_sphere (0 : ℂ) (r : ℝ)).exists_bound_of_continuousOn hcontr
  let MR : ℝ := max MR0 0
  let Mr : ℝ := max Mr0 0
  have hMR : ∀ z ∈ sphere (0 : ℂ) (R : ℝ), ‖f z‖ ≤ MR := by
    intro z hz
    exact le_trans (hMR0 z hz) (le_max_left _ _)
  have hMr : ∀ z ∈ sphere (0 : ℂ) (r : ℝ), ‖f z‖ ≤ Mr := by
    intro z hz
    exact le_trans (hMr0 z hz) (le_max_left _ _)
  have hposRatio_nonneg : 0 ≤ (RMid : ℝ) / (R : ℝ) := by
    exact div_nonneg RMid.2 hR0.le
  have hposRatio_lt_one : (RMid : ℝ) / (R : ℝ) < 1 := by
    exact (div_lt_one hR0).2 hRMidR
  have hnegRatio_nonneg : 0 ≤ (r : ℝ) / (rMid : ℝ) := by
    exact div_nonneg r.2 hrMid0.le
  have hnegRatio_lt_one : (r : ℝ) / (rMid : ℝ) < 1 := by
    exact (div_lt_one hrMid0).2 hrrMid
  have hrRefρU : rRef < ρU := lt_trans hrRefRRef hRRefρU
  have hrec :
      laurentTerm a =
        fun m : ℤ ↦
          Int.rec (fun n z ↦ posLaurentCoeff f RRef n * z ^ n)
            (fun n z ↦ negLaurentCoeff f rRef n * (z ^ (n + 1 : ℕ))⁻¹) m := by
    funext m
    cases m with
    | ofNat n =>
        funext z
        change posLaurentCoeff f RRef n * z ^ (n : ℤ) = posLaurentCoeff f RRef n * z ^ n
        rw [zpow_natCast]
    | negSucc n =>
        funext z
        change negLaurentCoeff f rRef n * z ^ (Int.negSucc n) =
          negLaurentCoeff f rRef n * (z ^ (n + 1 : ℕ))⁻¹
        rw [zpow_negSucc]
  have hpos :
      SummableUniformlyOn posTerm s := by
    -- The positive tail is dominated by a geometric series on the smaller closed subannulus.
    have hu :
        Summable (fun n : ℕ ↦ MR * (((RMid : ℝ) / (R : ℝ)) ^ n)) :=
      (summable_geometric_of_lt_one hposRatio_nonneg hposRatio_lt_one).mul_left MR
    refine (HasSumUniformlyOn.of_norm_le_summable hu ?_).summableUniformlyOn
    intro n z hz
    have hz_upper : ‖z‖ ≤ (RMid : ℝ) := by
      exact_mod_cast hz.2
    have hcoeff :
        ‖posLaurentCoeff f RRef n‖ ≤ MR / (R : ℝ) ^ n := by
      have htransport :
          posLaurentCoeff f RRef n = posLaurentCoeff f R n :=
        posCoeff_radiusInvariant hf
          (show ρL < RRef by exact lt_trans hρLr (lt_trans hrrRef hrRefRRef))
          hRRefR.le hRρU n
      rw [htransport]
      exact normPosLaurentCoeff_le_circleBound hR0 hMR n
    calc
      ‖posTerm n z‖ = ‖posLaurentCoeff f RRef n * z ^ n‖ := by rfl
      _ = ‖posLaurentCoeff f RRef n‖ * ‖z‖ ^ n := by rw [norm_mul, norm_pow]
      _ ≤ (MR / (R : ℝ) ^ n) * (RMid : ℝ) ^ n := by
        gcongr
      _ = MR * (((RMid : ℝ) / (R : ℝ)) ^ n) := by
        rw [div_pow, div_eq_mul_inv]
        ring
  have hneg :
      SummableUniformlyOn negTerm s := by
    -- The negative tail is dominated by the reciprocal geometric series coming from the inner
    -- contour.
    have hu :
        Summable (fun n : ℕ ↦ Mr * (((r : ℝ) / (rMid : ℝ)) ^ (n + 1))) := by
      simpa [pow_succ, mul_left_comm, mul_assoc, mul_comm] using
        (summable_geometric_of_lt_one hnegRatio_nonneg hnegRatio_lt_one).mul_left
          (Mr * ((r : ℝ) / (rMid : ℝ)))
    refine (HasSumUniformlyOn.of_norm_le_summable hu ?_).summableUniformlyOn
    intro n z hz
    have hz_lower : (rMid : ℝ) ≤ ‖z‖ := by
      exact_mod_cast hz.1
    have hcoeff :
        ‖negLaurentCoeff f rRef n‖ ≤ Mr * (r : ℝ) ^ (n + 1) := by
      have htransport :
          negLaurentCoeff f rRef n = negLaurentCoeff f r n :=
        (negLaurentCoeff_radiusInvariant hf hρLr hrrRef.le hrRefρU n).symm
      rw [htransport]
      exact normNegLaurentCoeff_le_circleBound hr0 hMr n
    have hInv :
        ((‖z‖ ^ (n + 1))⁻¹) ≤ (((rMid : ℝ) ^ (n + 1))⁻¹) := by
      have hpow : (rMid : ℝ) ^ (n + 1) ≤ ‖z‖ ^ (n + 1) := by
        gcongr
      have hrMidPow_pos : 0 < ((rMid : ℝ) ^ (n + 1)) := by
        positivity
      simpa [one_div] using
        (one_div_le_one_div_of_le hrMidPow_pos hpow)
    calc
      ‖negTerm n z‖ = ‖negLaurentCoeff f rRef n * z ^ (Int.negSucc n)‖ := by rfl
      _ = ‖negLaurentCoeff f rRef n‖ * ‖z‖ ^ (Int.negSucc n) := by
        rw [norm_mul, norm_zpow]
      _ = ‖negLaurentCoeff f rRef n‖ * ((‖z‖ ^ (n + 1))⁻¹) := by
        rw [zpow_negSucc]
      _ ≤ (Mr * (r : ℝ) ^ (n + 1)) * (((rMid : ℝ) ^ (n + 1))⁻¹) := by
        exact mul_le_mul hcoeff hInv (by positivity) (by positivity)
      _ = Mr * (((r : ℝ) / (rMid : ℝ)) ^ (n + 1)) := by
        rw [div_pow, div_eq_mul_inv]
        ring
  -- The Laurent family is the integer-indexed combination of these positive and negative tails.
  rw [hrec]
  exact summableUniformlyOn_intRec hpos hneg

/-- Helper for Cartan section10 frozen_0003_Theorem_III_4_extra_3: on a smaller closed
subannulus inside a finite ambient annulus, the fixed reference Laurent family sums back to `f`. -/
lemma referenceLaurentFamily_eqOn_closedSubannulus
    {ρL ρU r rRef rMid RMid RRef R : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρL ρU))
    (hρLr : ρL < r) (hrrRef : r < rRef) (hrRefRRef : rRef < RRef)
    (hRRefR : RRef < R) (hRρU : R < ρU)
    (hrrMid : r < rMid) (hrMidRMid : rMid ≤ RMid) (hRMidR : RMid < R) :
    Set.EqOn f
      (fun z : ℂ ↦
        ∑' m : ℤ, (Int.rec (posLaurentCoeff f RRef) (negLaurentCoeff f rRef) m) * z ^ m)
      (complexClosedAnnulus rMid RMid) := by
  let a : ℤ → ℂ := fun m ↦ Int.rec (posLaurentCoeff f RRef) (negLaurentCoeff f rRef) m
  have hrR : r < R := lt_trans hrrMid (lt_of_le_of_lt hrMidRMid hRMidR)
  have hρLR : ρL < R := lt_trans hρLr hrR
  have hrρU : r < ρU := lt_trans hrR hRρU
  have hRRefρU : RRef < ρU := lt_trans hRRefR hRρU
  have hrRefρU : rRef < ρU := lt_trans hrRefRRef hRRefρU
  have hsum :
      SummableUniformlyOn (laurentTerm a) (complexClosedAnnulus rMid RMid) :=
    referenceLaurentFamily_summableUniformlyOn_closedSubannulus
      hf hρLr hrrRef hrRefRRef hRRefR hRρU hrrMid hrMidRMid hRMidR
  intro z hz
  have hzr : (r : ℝ) < ‖z‖ := by
    exact_mod_cast lt_of_lt_of_le hrrMid hz.1
  have hzR : ‖z‖ < (R : ℝ) := by
    exact_mod_cast lt_of_le_of_lt hz.2 hRMidR
  have hzBallR : z ∈ ball (0 : ℂ) (R : ℝ) := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hzR
  have hzExteriorr : z ∈ (closedBall (0 : ℂ) (r : ℝ))ᶜ := by
    simpa [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero] using not_le_of_gt hzr
  have hsumSummable : Summable (fun m : ℤ ↦ a m * z ^ m) := by
    simpa [laurentTerm] using hsum.summable hz
  have hposSummable :
      Summable (fun n : ℕ ↦ posLaurentCoeff f RRef n * z ^ n) := by
    simpa [a] using hsumSummable.comp_injective Nat.cast_injective
  have hnegSummable :
      Summable (fun n : ℕ ↦ negLaurentCoeff f rRef n * z ^ (Int.negSucc n)) := by
    simpa [a] using hsumSummable.comp_injective (@Int.negSucc.inj)
  have hsplit :
      ∑' m : ℤ, a m * z ^ m =
        (∑' n : ℕ, posLaurentCoeff f RRef n * z ^ n) +
          ∑' n : ℕ, negLaurentCoeff f rRef n * (z ^ (n + 1 : ℕ))⁻¹ := by
    have hrecz :
        (fun m : ℤ ↦ a m * z ^ m) =
          fun m : ℤ ↦
            Int.rec (fun n ↦ posLaurentCoeff f RRef n * z ^ n)
              (fun n ↦ negLaurentCoeff f rRef n * (z ^ (n + 1 : ℕ))⁻¹) m := by
      funext m
      cases m with
      | ofNat n =>
          change posLaurentCoeff f RRef n * z ^ (n : ℤ) = posLaurentCoeff f RRef n * z ^ n
          rw [zpow_natCast]
      | negSucc n =>
          change negLaurentCoeff f rRef n * z ^ (Int.negSucc n) =
            negLaurentCoeff f rRef n * (z ^ (n + 1 : ℕ))⁻¹
          rw [zpow_negSucc]
    simpa [hrecz] using (tsum_int_rec hposSummable hnegSummable)
  have hposTransport :
      ∀ n : ℕ, posLaurentCoeff f R n = posLaurentCoeff f RRef n := by
    intro n
    exact (posCoeff_radiusInvariant hf
      (show ρL < RRef by exact lt_trans hρLr (lt_trans hrrRef hrRefRRef))
      hRRefR.le hRρU n).symm
  have hnegTransport :
      ∀ n : ℕ, negLaurentCoeff f r n = negLaurentCoeff f rRef n := by
    intro n
    exact negLaurentCoeff_radiusInvariant hf hρLr hrrRef.le hrRefρU n
  -- First rewrite the two Cauchy pieces into their positive and negative Laurent tails, then
  -- transport those tails back to the fixed reference coefficients.
  calc
    f z = circleInnerPiece f R z + circleOuterPiece f r z := by
      exact annulus_circle_piece_sum_eq hf hρLr hrR hRρU hzr hzR
    _ = (∑' n : ℕ, posLaurentCoeff f R n * z ^ n) +
          ∑' n : ℕ, negLaurentCoeff f r n * z ^ (Int.negSucc n) := by
            rw [circleInnerPiece_eq_posPowerSeriesOnBall hf hρLR hRρU hzBallR,
              circleOuterPiece_eq_negLaurentTailOnExterior hf hρLr hrρU hzExteriorr]
    _ = (∑' n : ℕ, posLaurentCoeff f RRef n * z ^ n) +
          ∑' n : ℕ, negLaurentCoeff f rRef n * z ^ (Int.negSucc n) := by
            congr 1
            · refine tsum_congr ?_
              intro n
              rw [hposTransport n]
            · refine tsum_congr ?_
              intro n
              rw [hnegTransport n]
    _ = (∑' n : ℕ, posLaurentCoeff f RRef n * z ^ n) +
          ∑' n : ℕ, negLaurentCoeff f rRef n * (z ^ (n + 1 : ℕ))⁻¹ := by
            refine congrArg (fun s : ℂ ↦ (∑' n : ℕ, posLaurentCoeff f RRef n * z ^ n) + s) ?_
            refine tsum_congr ?_
            intro n
            rw [zpow_negSucc]
    _ = ∑' m : ℤ, a m * z ^ m := by
      simpa using hsplit.symm

/-- Cartan section10 frozen_0003_Theorem_III_4_extra_3: any holomorphic function on the annulus
`ρ₂ < |z| < ρ₁` has a Laurent expansion there. -/
theorem AnalyticOnNhd.hasLaurentExpansionOnAnnulus
    {ρ₂ ρ₁ : ENNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁)) :
    HasLaurentExpansionOnAnnulus f ρ₂ ρ₁ := by
  by_cases hne : Set.Nonempty (complexOpenAnnulus ρ₂ ρ₁)
  · -- Route correction: the reciprocal substitution route was the wrong normal form. The stable
    -- path now uses the textbook coefficient formula directly: the positive branch already comes
    -- from `circleInnerPiece_eq_posPowerSeriesOnBall`, and the negative pointwise rewrite is now
    -- isolated in `circleOuterPiece_eq_negLaurentTailOnExterior`.
    rcases hne with ⟨zRef, hzRef⟩
    rcases (ENNReal.lt_iff_exists_nnreal_btwn.mp hzRef.1) with ⟨rRef, hρ₂rRef, hrRefzRef⟩
    rcases (ENNReal.lt_iff_exists_nnreal_btwn.mp hzRef.2) with ⟨RRef, hzRefRRef, hRRefρ₁⟩
    have hrRefRRef : rRef < RRef := by
      exact_mod_cast lt_trans hrRefzRef hzRefRRef
    let a : ℤ → ℂ := fun m ↦ Int.rec (posLaurentCoeff f RRef) (negLaurentCoeff f rRef) m
    have chooseLocalRadii :
        ∀ {z : ℂ}, z ∈ complexOpenAnnulus ρ₂ ρ₁ →
          ∃ ρL r rMid RMid R ρU : NNReal,
            ρ₂ < (ρL : ENNReal) ∧ (ρL : ENNReal) < r ∧ (r : ENNReal) < rRef ∧
              r < rMid ∧ (rMid : ENNReal) < ‖z‖₊ ∧ ‖z‖₊ < RMid ∧ RMid < R ∧
              (RRef : ENNReal) < R ∧ (R : ENNReal) < ρU ∧ (ρU : ENNReal) < ρ₁ := by
      intro z hz
      -- We choose local radii so that `r < rRef < RRef < R` and the evaluation point sits strictly
      -- inside the intermediate closed subannulus `rMid ≤ |z| ≤ RMid`.
      have hρ₂min : ρ₂ < ((min rRef ‖z‖₊ : NNReal) : ENNReal) := by
        simpa using (lt_min_iff.mpr ⟨hρ₂rRef, hz.1⟩)
      rcases (ENNReal.lt_iff_exists_nnreal_btwn.mp hρ₂min) with ⟨r, hρ₂r, hrmin⟩
      have hrrRef : (r : ENNReal) < rRef := by
        exact lt_of_lt_of_le hrmin (by exact_mod_cast min_le_left rRef ‖z‖₊)
      have hrz : (r : ENNReal) < ‖z‖₊ := by
        exact lt_of_lt_of_le hrmin (by exact_mod_cast min_le_right rRef ‖z‖₊)
      rcases exists_between (show r < ‖z‖₊ by exact_mod_cast hrz) with ⟨rMid, hrrMid, hrMidz⟩
      have hmaxρ₁ : (((max RRef ‖z‖₊ : NNReal) : ENNReal) < ρ₁) := by
        simpa using (max_lt_iff.mpr ⟨hRRefρ₁, hz.2⟩)
      rcases (ENNReal.lt_iff_exists_nnreal_btwn.mp hmaxρ₁) with ⟨R, hmaxR, hRρ₁⟩
      have hRRefR : (RRef : ENNReal) < R := by
        exact lt_of_le_of_lt (by exact_mod_cast le_max_left RRef ‖z‖₊) hmaxR
      have hzR : ‖z‖₊ < (R : ENNReal) := by
        exact lt_of_le_of_lt (by exact_mod_cast le_max_right RRef ‖z‖₊) hmaxR
      rcases exists_between (show ‖z‖₊ < R by exact_mod_cast hzR) with ⟨RMid, hzRMid, hRMidR⟩
      rcases (ENNReal.lt_iff_exists_nnreal_btwn.mp hρ₂r) with ⟨ρL, hρ₂ρL, hρLr⟩
      rcases (ENNReal.lt_iff_exists_nnreal_btwn.mp hRρ₁) with ⟨ρU, hRρU, hρUρ₁⟩
      exact ⟨ρL, r, rMid, RMid, R, ρU, hρ₂ρL, hρLr, hrrRef, hrrMid, by exact_mod_cast hrMidz,
        by exact_mod_cast hzRMid, hRMidR, hRRefR, hRρU, hρUρ₁⟩
    refine ⟨a, ?_, ?_⟩
    · -- The Laurent family is locally uniformly summable because every annulus point is contained
      -- in a smaller closed subannulus where the geometric M-test applies.
      refine summableLocallyUniformlyOn_of_of_forall_exists_nhds ?_
      intro z hz
      rcases chooseLocalRadii hz with
        ⟨ρL, r, rMid, RMid, R, ρU, hρ₂ρL, hρLr, hrrRef, hrrMid, hrMidz, hzRMid, hRMidR,
          hRRefR, hRρU, hρUρ₁⟩
      have hrMidz_nn : rMid < ‖z‖₊ := by
        exact_mod_cast hrMidz
      have hzRMid_nn : ‖z‖₊ < RMid := by
        exact_mod_cast hzRMid
      have hrMidRMid : rMid ≤ RMid := le_of_lt (lt_trans hrMidz_nn hzRMid_nn)
      have hsubset :
          complexOpenAnnulus ρL ρU ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
        intro w hw
        exact ⟨lt_trans hρ₂ρL hw.1, lt_trans hw.2 hρUρ₁⟩
      have hfLocal : AnalyticOnNhd ℂ f (complexOpenAnnulus ρL ρU) := hf.mono hsubset
      have hzBallRMid : z ∈ ball (0 : ℂ) (RMid : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using
          (show ‖z‖ < (RMid : ℝ) by exact_mod_cast hzRMid_nn)
      have hzNotClosedBallrMid : z ∉ closedBall (0 : ℂ) (rMid : ℝ) := by
        simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using
          not_le_of_gt (show (rMid : ℝ) < ‖z‖ by exact_mod_cast hrMidz_nn)
      have hclosedNhds : complexClosedAnnulus rMid RMid ∈ 𝓝 z := by
        -- The strict inequalities `rMid < |z| < RMid` make the closed subannulus a genuine
        -- neighborhood of `z`.
        have hclosedBall : closedBall (0 : ℂ) (RMid : ℝ) ∈ 𝓝 z :=
          Metric.closedBall_mem_nhds_of_mem hzBallRMid
        have houter : (closedBall (0 : ℂ) (rMid : ℝ))ᶜ ∈ 𝓝 z :=
          isClosed_closedBall.isOpen_compl.mem_nhds hzNotClosedBallrMid
        refine Filter.mem_of_superset (Filter.inter_mem hclosedBall houter) ?_
        intro w hw
        refine ⟨?_, ?_⟩
        · have hwOuter : w ∉ closedBall (0 : ℂ) (rMid : ℝ) := hw.2
          exact_mod_cast (lt_of_not_ge (by
            simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hwOuter)).le
        · exact_mod_cast (by
            simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hw.1 : ‖w‖ ≤ (RMid : ℝ))
      have hwithin :
          complexClosedAnnulus rMid RMid ∈ 𝓝[complexOpenAnnulus ρ₂ ρ₁] z := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        refine ⟨complexClosedAnnulus rMid RMid, hclosedNhds, ?_⟩
        intro w hw
        exact hw.1
      refine ⟨complexClosedAnnulus rMid RMid, hwithin, ?_⟩
      exact referenceLaurentFamily_summableUniformlyOn_closedSubannulus
        hfLocal (show ρL < r by exact_mod_cast hρLr) (show r < rRef by exact_mod_cast hrrRef)
        hrRefRRef (show RRef < R by exact_mod_cast hRRefR) (show R < ρU by exact_mod_cast hRρU)
        hrrMid hrMidRMid hRMidR
    · -- Pointwise equality follows by applying the closed-subannulus contour decomposition on a
      -- neighborhood-sized annulus around each annulus point.
      intro z hz
      rcases chooseLocalRadii hz with
        ⟨ρL, r, rMid, RMid, R, ρU, hρ₂ρL, hρLr, hrrRef, hrrMid, hrMidz, hzRMid, hRMidR,
          hRRefR, hRρU, hρUρ₁⟩
      have hrMidz_nn : rMid < ‖z‖₊ := by
        exact_mod_cast hrMidz
      have hzRMid_nn : ‖z‖₊ < RMid := by
        exact_mod_cast hzRMid
      have hrMidRMid : rMid ≤ RMid := le_of_lt (lt_trans hrMidz_nn hzRMid_nn)
      have hsubset :
          complexOpenAnnulus ρL ρU ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
        intro w hw
        exact ⟨lt_trans hρ₂ρL hw.1, lt_trans hw.2 hρUρ₁⟩
      have hfLocal : AnalyticOnNhd ℂ f (complexOpenAnnulus ρL ρU) := hf.mono hsubset
      have hzClosed : z ∈ complexClosedAnnulus rMid RMid := by
        exact ⟨le_of_lt hrMidz_nn, le_of_lt hzRMid_nn⟩
      simpa [a] using
        (referenceLaurentFamily_eqOn_closedSubannulus hfLocal
          (show ρL < r by exact_mod_cast hρLr) (show r < rRef by exact_mod_cast hrrRef)
          hrRefRRef (show RRef < R by exact_mod_cast hRRefR) (show R < ρU by exact_mod_cast hRρU)
          hrrMid hrMidRMid hRMidR hzClosed)
  · -- If the annulus is empty, the zero Laurent family is a vacuous expansion there.
    refine ⟨fun _ ↦ 0, ?_, ?_⟩
    · -- Local uniform summability on the empty annulus is immediate because there are no points.
      refine summableLocallyUniformlyOn_of_of_forall_exists_nhds ?_
      intro z hz
      exact False.elim (hne ⟨z, hz⟩)
    · -- Equality on the empty annulus is vacuous as well.
      intro z hz
      exact False.elim (hne ⟨z, hz⟩)
