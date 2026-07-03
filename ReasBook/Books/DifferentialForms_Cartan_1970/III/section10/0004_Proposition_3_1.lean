import Mathlib
import DifferentialForms_Cartan_1970.II.section06.«0009_Example_II_2_extra_3»
import DifferentialForms_Cartan_1970.III.section10.«0003_Theorem_III_4_extra_3»

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: `lean_leansearch` was unavailable here; the statement shape was checked
-- against local archived precedent using `AnalyticOnNhd` on the annulus, disc, and exterior region.

open scoped Topology
open Metric

noncomputable section

/-- Helper for Proposition 3.1: the open annulus is an open subset of `ℂ`. -/
lemma isOpen_complexOpenAnnulus (ρ₂ ρ₁ : ENNReal) : IsOpen (complexOpenAnnulus ρ₂ ρ₁) := by
  -- Both defining norm inequalities are open conditions, so their conjunction is open as well.
  simpa [complexOpenAnnulus] using
    (isOpen_lt (continuous_const : Continuous fun _ : ℂ ↦ ρ₂)
      (ENNReal.continuous_coe.comp continuous_nnnorm)).inter
      (isOpen_lt (ENNReal.continuous_coe.comp continuous_nnnorm)
        (continuous_const : Continuous fun _ : ℂ ↦ ρ₁))

/-- Helper for Proposition 3.1: the Laurent sum attached to a locally uniformly convergent Laurent
series is analytic on the ambient annulus. -/
lemma laurent_sum_analyticOnNhd_complexOpenAnnulus
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁) :
    AnalyticOnNhd ℂ (fun z ↦ ∑' n : ℤ, a n * z ^ n) (complexOpenAnnulus ρ₂ ρ₁) := by
  have hopen : IsOpen (complexOpenAnnulus (ρ₂ : ENNReal) (ρ₁ : ENNReal)) :=
    isOpen_complexOpenAnnulus _ _
  have hdiff :
      DifferentiableOn ℂ (fun z ↦ ∑' n : ℤ, laurentTerm a n z) (complexOpenAnnulus ρ₂ ρ₁) := by
    -- Each Laurent monomial is differentiable away from the origin, and annulus points are
    -- automatically nonzero.
    refine ha.differentiableOn hopen ?_
    intro n z hz
    change ((ρ₂ : ENNReal) < (‖z‖₊ : ENNReal) ∧ (‖z‖₊ : ENNReal) < (ρ₁ : ENNReal)) at hz
    have hz0 : z ≠ 0 := by
      intro hz0
      exact (not_lt_of_ge (bot_le : (0 : ENNReal) ≤ ρ₂)) (by simpa [hz0] using hz.1)
    simpa [laurentTerm] using (differentiableAt_id.zpow (m := n) (Or.inl hz0)).const_mul (a n)
  -- Convert differentiability on the open annulus into analyticity there.
  simpa [laurentTerm] using hdiff.analyticOnNhd hopen

/-- Helper for Proposition 3.1: a circle whose radius lies strictly between `ρ₂` and `ρ₁`
is contained in the annulus `ρ₂ < ‖z‖ < ρ₁`. -/
lemma sphere_subset_complexOpenAnnulus_of_lt_lt
    {ρ₂ ρ₁ R : NNReal} (hρ₂ : ρ₂ < R) (hρ₁ : R < ρ₁) :
    sphere (0 : ℂ) (R : ℝ) ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
  -- Points on the radius-`R` circle satisfy the defining norm inequalities of the annulus
  -- exactly because their norm is `R`.
  intro z hz
  have hzR : ‖z‖ = (R : ℝ) := by
    simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
  have hzR' : ‖z‖₊ = R := by
    exact NNReal.coe_injective (by simpa using hzR)
  change (ρ₂ : ENNReal) < ‖z‖₊ ∧ ‖z‖₊ < (ρ₁ : ENNReal)
  constructor
  · simpa [hzR'] using (show (ρ₂ : ENNReal) < (R : ENNReal) by exact_mod_cast hρ₂)
  · simpa [hzR'] using (show (R : ENNReal) < (ρ₁ : ENNReal) by exact_mod_cast hρ₁)

/-- Helper for Proposition 3.1: the radius-`R` circle sits in the degenerate closed annulus
`R ≤ ‖z‖ ≤ R`. -/
lemma sphere_subset_complexClosedAnnulus_eq_radius
    {R : NNReal} :
    sphere (0 : ℂ) (R : ℝ) ⊆ complexClosedAnnulus R R := by
  -- Points on the sphere satisfy both closed-annulus inequalities by the exact norm identity.
  intro z hz
  have hzR : ‖z‖ = (R : ℝ) := by
    simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
  have hzR' : ‖z‖₊ = R := by
    exact NNReal.coe_injective (by simpa using hzR)
  exact ⟨by simp [hzR'], by simp [hzR']⟩

/-- Helper for Proposition 3.1: the Laurent family is uniformly summable on every intermediate
circle after restricting the closed-annulus summability theorem to that sphere. -/
lemma laurent_summableUniformlyOn_sphere
    {a : ℤ → ℂ} {ρ₂ ρ₁ R : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    (hρ₂R : ρ₂ < R) (hRρ₁ : R < ρ₁) :
    SummableUniformlyOn (laurentTerm a) (sphere (0 : ℂ) (R : ℝ)) := by
  -- First obtain uniform summability on the degenerate closed annulus `R ≤ ‖z‖ ≤ R`.
  have hclosed :
      SummableUniformlyOn (laurentTerm a) (complexClosedAnnulus R R) :=
    ha.summableUniformlyOn_closedAnnulus (r₂ := R) (r₁ := R)
      (by exact_mod_cast hρ₂R) (by exact_mod_cast hRρ₁)
  -- Then restrict that uniform summability to the sphere itself.
  exact hclosed.mono sphere_subset_complexClosedAnnulus_eq_radius

/-- Helper for Proposition 3.1: the outer-circle Cauchy transform that will supply the inner
holomorphic summand. -/
noncomputable def circleInnerPiece (f : ℂ → ℂ) (R : NNReal) : ℂ → ℂ :=
  fun z ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ t in C(0, (R : ℝ)), (t - z)⁻¹ • f t

/-- Helper for Proposition 3.1: the Laurent sum is circle-integrable on any intermediate circle
inside the annulus. -/
lemma laurent_sum_circleIntegrable
    {a : ℤ → ℂ} {ρ₂ ρ₁ R : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    (hρ₂ : ρ₂ < R) (hρ₁ : R < ρ₁) :
    CircleIntegrable (fun z ↦ ∑' n : ℤ, a n * z ^ n) 0 (R : ℝ) := by
  -- The annulus Laurent sum is analytic on a neighborhood of the circle, hence continuous there.
  have hsphere :
      sphere (0 : ℂ) (R : ℝ) ⊆ complexOpenAnnulus ρ₂ ρ₁ :=
    sphere_subset_complexOpenAnnulus_of_lt_lt hρ₂ hρ₁
  have hcont :
      ContinuousOn (fun z ↦ ∑' n : ℤ, a n * z ^ n) (sphere (0 : ℂ) (R : ℝ)) :=
    (laurent_sum_analyticOnNhd_complexOpenAnnulus ha).continuousOn.mono hsphere
  exact hcont.circleIntegrable R.2

/-- Helper for Proposition 3.1: the Cauchy transform over a circle inside the annulus is analytic
on the enclosed disc. -/
lemma circleInnerPiece_analyticOnNhd
    {ρ₂ ρ₁ R : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁))
    (hρ₂ : ρ₂ < R) (hρ₁ : R < ρ₁) :
    AnalyticOnNhd ℂ (circleInnerPiece f R) (ball (0 : ℂ) R) := by
  -- The boundary values are continuous on the chosen circle because the annulus analyticity gives
  -- continuity on every smaller closed subset.
  have hsphere :
      sphere (0 : ℂ) (R : ℝ) ⊆ complexOpenAnnulus ρ₂ ρ₁ :=
    sphere_subset_complexOpenAnnulus_of_lt_lt hρ₂ hρ₁
  have hcont : ContinuousOn f (sphere (0 : ℂ) (R : ℝ)) :=
    hf.continuousOn.mono hsphere
  have hcircle : CircleIntegrable f 0 (R : ℝ) :=
    hcont.circleIntegrable R.2
  have hR0 : 0 < R := lt_of_le_of_lt ρ₂.2 hρ₂
  -- Mathlib's Cauchy-integral power-series theorem gives analyticity on the full disc.
  convert
      (hasFPowerSeriesOn_cauchy_integral (c := (0 : ℂ)) (R := R) hcircle hR0).analyticOnNhd using
    1
  ext z
  simp

/-- Helper for Proposition 3.1: the inner-circle Cauchy transform carrying the exterior
holomorphic summand. -/
noncomputable def circleOuterPiece (f : ℂ → ℂ) (r : NNReal) : ℂ → ℂ :=
  fun z ↦ -((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ t in C(0, (r : ℝ)), (t - z)⁻¹ • f t)

/-- Helper for Proposition 3.1: on every overlap annulus, the outer-circle and inner-circle
Cauchy pieces add back up to the original function. -/
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
  have hz_not_ballr : z ∉ ball (0 : ℂ) (r : ℝ) := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using not_lt_of_ge hzr.le
  have hz_not_closedBallr : z ∉ closedBall (0 : ℂ) (r : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using not_le_of_gt hzr
  have hsphereR :
      sphere (0 : ℂ) (R : ℝ) ⊆ complexOpenAnnulus ρ₂ ρ₁ :=
    sphere_subset_complexOpenAnnulus_of_lt_lt (R := R) (lt_trans hρ₂r hrR) hRρ₁
  have hspherer :
      sphere (0 : ℂ) (r : ℝ) ⊆ complexOpenAnnulus ρ₂ ρ₁ :=
    sphere_subset_complexOpenAnnulus_of_lt_lt (R := r) hρ₂r (lt_trans hrR hRρ₁)
  have hclosedAnnulus_subset : closedAnnulus ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
    -- Every point in the geometric closed annulus satisfies the strict bounds inherited from `r`
    -- and `R`.
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
    -- The open annulus inherits the same two radius inequalities.
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
    -- Replacing the pole by the dslope removes the singularity at `z`.
    exact (continuousOn_dslope hclosedAnnulus_nhds).2 ⟨hcont_closedAnnulus, (hf z hzAnn).differentiableAt⟩
  have hdslope_diff :
      ∀ w ∈ puncturedAnnulus \ badSet, DifferentiableAt ℂ (dslope f z) w := by
    -- Away from the removed point `z`, dslope has the same differentiability as `f`.
    intro w hw
    have hw_ne : w ≠ z := by
      simpa [badSet] using hw.2
    exact (differentiableAt_dslope_of_ne hw_ne).2 ((hf w (hpuncturedAnnulus_subset hw.1)).differentiableAt)
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
  have houter_inv_cont : ContinuousOn (fun w : ℂ ↦ (w - z)⁻¹) (sphere (0 : ℂ) (R : ℝ)) :=
    ((continuousOn_id.sub continuousOn_const).inv₀ fun w hw ↦ sub_ne_zero.2 (houter_ne w hw))
  have hinner_inv_cont : ContinuousOn (fun w : ℂ ↦ (w - z)⁻¹) (sphere (0 : ℂ) (r : ℝ)) :=
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
    -- The same dslope decomposition works on the inner circle.
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
    -- Comparing the outer and inner dslope integrals isolates exactly the residue contribution.
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
    have houter_eq := sub_eq_iff_eq_add.mp houter_minus_inner
    calc
      (∮ w in C(0, (R : ℝ)), (w - z)⁻¹ • f w) -
          ∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f w
        = ((∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f w) +
              (2 * Real.pi * Complex.I : ℂ) • f z) -
            ∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f w := by rw [houter_eq]
      _ = (2 * Real.pi * Complex.I : ℂ) • f z := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have htwo_pi_i_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hdiff_mul :
      (∮ w in C(0, (R : ℝ)), (w - z)⁻¹ • f w) -
        ∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f w = (2 * Real.pi * Complex.I : ℂ) * f z := by
    simpa [smul_eq_mul] using hdiff
  have hdecomp :
      circleInnerPiece f R z + circleOuterPiece f r z =
        ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ((∮ w in C(0, (R : ℝ)), (w - z)⁻¹ • f w) -
            ∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f w) := by
    -- Package the two circle pieces into one shared scalar factor.
    simp [circleInnerPiece, circleOuterPiece, smul_eq_mul, sub_eq_add_neg]
    ring
  have hcancel :
      ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ((2 * Real.pi * Complex.I : ℂ) * f z) = f z := by
    calc
      ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ((2 * Real.pi * Complex.I : ℂ) * f z)
        = (((2 * Real.pi * Complex.I : ℂ)⁻¹) * (2 * Real.pi * Complex.I : ℂ)) * f z := by
            ring
      _ = f z := by rw [inv_mul_cancel₀ htwo_pi_i_ne, one_mul]
  calc
    f z = ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ((2 * Real.pi * Complex.I : ℂ) * f z) := by
      exact hcancel.symm
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ((∮ w in C(0, (R : ℝ)), (w - z)⁻¹ • f w) -
            ∮ w in C(0, (r : ℝ)), (w - z)⁻¹ • f w) := by
      rw [hdiff_mul]
    _ = circleInnerPiece f R z + circleOuterPiece f r z := by
      rw [hdecomp]

/-- Helper for Proposition 3.1: on the annulus, the nonnegative Laurent tail is pointwise
summable. -/
lemma laurent_nonneg_part_summable
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    {z : ℂ} (hz : z ∈ complexOpenAnnulus ρ₂ ρ₁) :
    Summable (fun n : ℕ ↦ a (n : ℤ) * z ^ n) := by
  -- Restrict the annulus Laurent sum to the nonnegative indices.
  have hzsum : Summable (fun n : ℤ ↦ a n * z ^ n) := ha.summable hz
  simpa using hzsum.comp_injective Nat.cast_injective

/-- Helper for Proposition 3.1: on the annulus, the negative Laurent tail is pointwise
summable. -/
lemma laurent_neg_part_summable
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    {z : ℂ} (hz : z ∈ complexOpenAnnulus ρ₂ ρ₁) :
    Summable (fun n : ℕ ↦ a (Int.negSucc n) * z ^ (Int.negSucc n)) := by
  -- Restrict the annulus Laurent sum to the negative indices.
  have hzsum : Summable (fun n : ℤ ↦ a n * z ^ n) := ha.summable hz
  simpa using hzsum.comp_injective (@Int.negSucc.inj)

/-- Helper for Proposition 3.1: at a nonzero point, the negative Laurent tail can be rewritten as
`z⁻¹` times an ordinary power series in `z⁻¹`. -/
lemma laurent_neg_part_eq_inv_mul_powerSeries
    {a : ℤ → ℂ} {z : ℂ} (hz : z ≠ 0) :
    (∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n)) =
      z⁻¹ * ∑' n : ℕ, a (Int.negSucc n) * (z⁻¹) ^ n := by
  -- Rewrite each negative Laurent monomial using `zpow_negSucc`, then factor out `z⁻¹`.
  calc
    (∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n))
      = ∑' n : ℕ, z⁻¹ * (a (Int.negSucc n) * (z⁻¹) ^ n) := by
          refine tsum_congr ?_
          intro n
          calc
            a (Int.negSucc n) * z ^ (Int.negSucc n)
                = a (Int.negSucc n) * ((z ^ (n + 1))⁻¹) := by
                    rw [zpow_negSucc]
            _ = a (Int.negSucc n) * ((z ^ n * z)⁻¹) := by
                  rw [pow_succ]
            _ = a (Int.negSucc n) * (z⁻¹ * (z ^ n)⁻¹) := by
                  rw [mul_inv_rev]
            _ = z⁻¹ * (a (Int.negSucc n) * (z ^ n)⁻¹) := by
                  ac_rfl
            _ = z⁻¹ * (a (Int.negSucc n) * (z⁻¹) ^ n) := by
                  rw [inv_pow]
    _ = z⁻¹ * ∑' n : ℕ, a (Int.negSucc n) * (z⁻¹) ^ n := by
          rw [tsum_mul_left]

/-- Helper for Proposition 3.1: on the annulus, the Laurent sum splits into its nonnegative and
negative tails. -/
lemma laurent_split_eqOn_annulus
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} {f : ℂ → ℂ}
    (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    (hEq : Set.EqOn f (fun z ↦ ∑' n : ℤ, a n * z ^ n) (complexOpenAnnulus ρ₂ ρ₁)) :
    Set.EqOn f
      (fun z ↦ (∑' n : ℕ, a (n : ℤ) * z ^ n) + ∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n))
      (complexOpenAnnulus ρ₂ ρ₁) := by
  intro z hz
  have hnonneg := laurent_nonneg_part_summable ha hz
  have hneg := laurent_neg_part_summable ha hz
  let fNat : ℕ → ℂ := fun n ↦ a (n : ℤ) * z ^ n
  let gNeg : ℕ → ℂ := fun n ↦ a (Int.negSucc n) * z ^ (Int.negSucc n)
  have hrec : (fun n : ℤ ↦ Int.rec fNat gNeg n) = fun n : ℤ ↦ a n * z ^ n := by
    -- `Int.rec` is exactly the partition of `ℤ` into `Nat.cast` and `Int.negSucc`.
    funext n
    cases n <;> rfl
  -- Reindex the integer Laurent sum along `Int.ofNat ⊕ Int.negSucc`.
  calc
    f z = ∑' n : ℤ, a n * z ^ n := hEq hz
    _ = ∑' n : ℤ, Int.rec fNat gNeg n := by simpa [hrec]
    _ = (∑' n : ℕ, fNat n) + ∑' n : ℕ, gNeg n := by
          exact tsum_int_rec hnonneg hneg
    _ = (∑' n : ℕ, a (n : ℤ) * z ^ n) + ∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n) := by
          rfl

/-- Helper for Proposition 3.1: every point of the smaller disc admits an intermediate circle
that still lies inside the original annulus. -/
lemma exists_intermediate_radius_for_ball_point
    {ρ₂ ρ₁ : NNReal} (hρ : ρ₂ < ρ₁) {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ₁) :
    ∃ R : NNReal, max ρ₂ ‖z‖₊ < R ∧ R < ρ₁ := by
  -- The disc hypothesis gives `‖z‖ < ρ₁`, so there is room to choose a radius strictly between
  -- `max ρ₂ ‖z‖` and `ρ₁`.
  have hzlt : ‖z‖₊ < ρ₁ := by
    exact_mod_cast (by simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hz : ‖z‖ < (ρ₁ : ℝ))
  have hmax : max ρ₂ ‖z‖₊ < ρ₁ := max_lt_iff.mpr ⟨hρ, hzlt⟩
  exact exists_between hmax

/-- Helper for Proposition 3.1: every point of the exterior admits an intermediate inner circle
strictly between the boundary radius `ρ₂` and the point's norm. -/
lemma exists_intermediate_radius_for_exterior_point
    {ρ₂ : NNReal} {z : ℂ} (hz : z ∈ (closedBall (0 : ℂ) ρ₂)ᶜ) :
    ∃ r : NNReal, ρ₂ < r ∧ r < ‖z‖₊ := by
  -- The exterior condition is exactly the strict inequality `ρ₂ < ‖z‖`.
  have hzgt : ρ₂ < ‖z‖₊ := by
    have hznot : ¬ ‖z‖ ≤ (ρ₂ : ℝ) := by
      simpa [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
    exact_mod_cast lt_of_not_ge hznot
  exact exists_between hzgt

/-- Helper for Proposition 3.1: for an exterior point one can choose an intermediate inner radius
that still stays below both the outer annulus radius `ρ₁` and the point's norm. -/
lemma exists_intermediate_radius_for_exterior_point_lt_upper
    {ρ₂ ρ₁ : NNReal} (hρ : ρ₂ < ρ₁) {z : ℂ} (hz : z ∈ (closedBall (0 : ℂ) ρ₂)ᶜ) :
    ∃ r : NNReal, ρ₂ < r ∧ r < ρ₁ ∧ r < ‖z‖₊ := by
  -- We choose `r` between `ρ₂` and the smaller of `ρ₁` and `‖z‖`, so the reciprocal circle still
  -- lands inside the original annulus.
  have hzgt : ρ₂ < ‖z‖₊ := by
    rcases exists_intermediate_radius_for_exterior_point (ρ₂ := ρ₂) hz with ⟨r, hρ₂r, hrz⟩
    exact lt_trans hρ₂r hrz
  rcases exists_between (lt_min hρ hzgt) with ⟨r, hρ₂r, hrmin⟩
  exact ⟨r, hρ₂r, lt_of_lt_of_le hrmin (min_le_left _ _), lt_of_lt_of_le hrmin (min_le_right _ _)⟩

/-- Helper for Proposition 3.1: the circle integral of `z ^ k` detects only the residue term
`k = -1`. -/
lemma circleIntegral_zpow_eq_residue {R : ℝ} (hR : 0 < R) (k : ℤ) :
    (∮ z in C(0, R), z ^ k) = if k = -1 then 2 * Real.pi * Complex.I else 0 := by
  by_cases hk : k = -1
  · -- The residue case is exactly the basic Cauchy kernel integral.
    rw [if_pos hk]
    subst hk
    have hzero_mem : (0 : ℂ) ∈ ball (0 : ℂ) R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hR
    simpa using
      (circleIntegral.integral_sub_inv_of_mem_ball (c := (0 : ℂ)) (w := (0 : ℂ)) (R := R) hzero_mem)
  · -- Every other Laurent monomial has zero integral around the circle.
    rw [if_neg hk]
    simpa using
      (circleIntegral.integral_sub_zpow_of_ne hk (c := (0 : ℂ)) (w := (0 : ℂ)) (R := R))

/-- Helper for Proposition 3.1: uniform convergence of a Laurent family on a circle allows
termwise circle integration. -/
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

/-- Helper for Proposition 3.1: points on a positive-radius circle are nonzero. -/
lemma ne_zero_of_mem_sphere_zero_of_pos {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) R) : z ≠ 0 := by
  -- A point on `sphere 0 R` has norm `R`, so for `R > 0` it cannot be the origin.
  have hzR : ‖z‖ = R := by
    simpa using mem_sphere_iff_norm.mp hz
  exact fun hz0 ↦ (ne_of_gt hR) <| by simpa [hz0] using hzR.symm

/-- Helper for Proposition 3.1: each Laurent monomial is continuous on a positive-radius circle. -/
lemma laurentTerm_continuousOn_sphere
    {a : ℤ → ℂ} {R : NNReal} (hR : 0 < (R : ℝ)) (m : ℤ) :
    ContinuousOn (laurentTerm a m) (sphere (0 : ℂ) (R : ℝ)) := by
  -- The only issue for a `zpow` monomial is the origin, and a positive-radius circle avoids it.
  refine (continuousOn_const.mul (continuousOn_zpow₀ (m := m))).mono ?_
  intro z hz
  exact ne_zero_of_mem_sphere_zero_of_pos hR hz

/-- Helper for Proposition 3.1: multiplying a locally uniformly summable series by a fixed
continuous factor preserves local uniform summability on the same set. -/
lemma hasSumLocallyUniformlyOn_mul_fixed
    {X ι : Type*} [TopologicalSpace X] {s : Set X} {F : ι → X → ℂ} {G g : X → ℂ}
    (h : HasSumLocallyUniformlyOn F G s) (hg : ContinuousOn g s) (hG : ContinuousOn G s) :
    HasSumLocallyUniformlyOn (fun i x ↦ g x * F i x) (fun x ↦ g x * G x) s := by
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h ⊢
  have hconst : TendstoLocallyUniformlyOn (fun _ : Finset ι => g) g Filter.atTop s := by
    -- The constant family already agrees pointwise with its limit, so local uniform convergence is
    -- immediate from reflexivity of each entourage.
    intro u hu x hx
    refine ⟨s, self_mem_nhdsWithin, ?_⟩
    filter_upwards with n y hy
    exact refl_mem_uniformity hu
  -- Multiply the partial sums by the fixed factor before rewriting the finite sums.
  refine (hconst.mul₀ h hg hG).congr ?_
  intro t
  intro x hx
  simp [Finset.mul_sum, mul_assoc]

/-- Helper for Proposition 3.1: on a compact set, local uniform summability upgrades to uniform
summability. -/
lemma hasSumUniformlyOn_of_hasSumLocallyUniformlyOn_isCompact
    {X ι : Type*} [TopologicalSpace X] {s : Set X} {F : ι → X → ℂ} {G : X → ℂ}
    (hs : IsCompact s) (h : HasSumLocallyUniformlyOn F G s) :
    HasSumUniformlyOn F G s := by
  -- Compactness identifies locally uniform convergence with uniform convergence on `s`.
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hs]
  exact hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp h

/-- Helper for Proposition 3.1: multiplying the Laurent family on a fixed sphere by the fixed
shift `z ^ (Int.negSucc n)` preserves the uniform summability needed for termwise circle
integration. -/
lemma shifted_laurent_summableUniformlyOn_sphere
    {a : ℤ → ℂ} {ρ₂ ρ₁ R : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    (hρ₂R : ρ₂ < R) (hRρ₁ : R < ρ₁) (n : ℕ) :
    SummableUniformlyOn
      (fun m z ↦ z ^ (Int.negSucc n) * laurentTerm a m z)
      (sphere (0 : ℂ) (R : ℝ)) := by
  let s : Set ℂ := sphere (0 : ℂ) (R : ℝ)
  have hR0 : 0 < (R : ℝ) := by
    exact_mod_cast lt_of_le_of_lt ρ₂.2 hρ₂R
  have hsphere : s ⊆ complexOpenAnnulus ρ₂ ρ₁ :=
    sphere_subset_complexOpenAnnulus_of_lt_lt hρ₂R hRρ₁
  have hbase :
      HasSumLocallyUniformlyOn (laurentTerm a) (fun z ↦ ∑' m : ℤ, laurentTerm a m z) s :=
    ha.hasSumLocallyUniformlyOn.mono hsphere
  have hshift_cont : ContinuousOn (fun z : ℂ ↦ z ^ (Int.negSucc n)) s := by
    -- On a positive-radius circle the shift factor is a continuous `zpow`.
    refine ((continuousOn_zpow₀ (m := Int.negSucc n)).mono ?_)
    intro z hz
    exact ne_zero_of_mem_sphere_zero_of_pos hR0 hz
  have hsum_cont : ContinuousOn (fun z : ℂ ↦ ∑' m : ℤ, laurentTerm a m z) s :=
    (laurent_sum_analyticOnNhd_complexOpenAnnulus (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) ha).continuousOn.mono
      hsphere
  have hshifted :
      HasSumLocallyUniformlyOn
        (fun m z ↦ z ^ (Int.negSucc n) * laurentTerm a m z)
        (fun z ↦ z ^ (Int.negSucc n) * ∑' m : ℤ, laurentTerm a m z) s :=
    hasSumLocallyUniformlyOn_mul_fixed hbase hshift_cont hsum_cont
  have hscompact : IsCompact s := by
    simpa [s] using isCompact_sphere (0 : ℂ) (R : ℝ)
  have huniform :
      HasSumUniformlyOn
        (fun m z ↦ z ^ (Int.negSucc n) * laurentTerm a m z)
        (fun z ↦ z ^ (Int.negSucc n) * ∑' m : ℤ, laurentTerm a m z) s :=
    hasSumUniformlyOn_of_hasSumLocallyUniformlyOn_isCompact hscompact hshifted
  -- Only the uniform summability survives into the circle-integration step.
  exact huniform.summableUniformlyOn

/-- Helper for Proposition 3.1: after multiplying the Laurent family by the fixed shift
`z ^ (Int.negSucc n)` on the radius-`R` circle, one may still integrate the series termwise. -/
lemma circleIntegral_tsum_cauchy_nonneg_laurent_family
    {a : ℤ → ℂ} {ρ₂ ρ₁ R : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    (hρ₂R : ρ₂ < R) (hRρ₁ : R < ρ₁) (n : ℕ) :
    (∮ z in C(0, (R : ℝ)), ∑' m : ℤ, z ^ (Int.negSucc n) * laurentTerm a m z) =
      ∑' m : ℤ, ∮ z in C(0, (R : ℝ)), z ^ (Int.negSucc n) * laurentTerm a m z := by
  have hR0 : 0 < (R : ℝ) := by
    exact_mod_cast lt_of_le_of_lt ρ₂.2 hρ₂R
  have hshifted :
      SummableUniformlyOn
        (fun m z ↦ z ^ (Int.negSucc n) * laurentTerm a m z)
        (sphere (0 : ℂ) (R : ℝ)) :=
    shifted_laurent_summableUniformlyOn_sphere
      (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) (R := R) ha hρ₂R hRρ₁ n
  -- The shifted family inherits uniform summability on the circle, so termwise circle
  -- integration applies directly.
  exact
    circleIntegral_tsum_of_summableUniformlyOn_sphere
      (R := R)
      (F := fun m z ↦ z ^ (Int.negSucc n) * laurentTerm a m z)
      (fun m ↦
        ((continuousOn_zpow₀ (m := Int.negSucc n)).mono fun z hz ↦
          ne_zero_of_mem_sphere_zero_of_pos hR0 hz).mul
          (laurentTerm_continuousOn_sphere (a := a) hR0 m))
      hshifted

/-- Helper for Proposition 3.1: at a nonzero point, the direct Cauchy integrand is exactly the
shifted Laurent `tsum` used to isolate the nonnegative coefficient. -/
lemma cauchy_nonneg_integrand_eq_shifted_tsum
    {a : ℤ → ℂ} {z : ℂ} (hz0 : z ≠ 0)
    (hsumz : Summable (fun m : ℤ ↦ a m * z ^ m)) (n : ℕ) :
    (1 / z) ^ n • z⁻¹ • (∑' m : ℤ, a m * z ^ m) =
      ∑' m : ℤ, z ^ (Int.negSucc n) * laurentTerm a m z := by
  -- Rewrite the Cauchy kernel as one negative-power factor, then move that fixed factor through
  -- the Laurent sum.
  calc
    (1 / z) ^ n • z⁻¹ • (∑' m : ℤ, a m * z ^ m)
      = z ^ (Int.negSucc n) * ∑' m : ℤ, a m * z ^ m := by
          rw [smul_eq_mul, smul_eq_mul]
          calc
            (1 / z : ℂ) ^ n * (z⁻¹ * ∑' m : ℤ, a m * z ^ m)
                = (((1 / z : ℂ) ^ n) * z⁻¹) * ∑' m : ℤ, a m * z ^ m := by ring
            _ = z ^ (Int.negSucc n) * ∑' m : ℤ, a m * z ^ m := by
                congr 1
                calc
                  ((1 / z : ℂ) ^ n) * z⁻¹ = (z ^ n)⁻¹ * z⁻¹ := by simp [one_div]
                  _ = z⁻¹ * (z ^ n)⁻¹ := by ac_rfl
                  _ = (z ^ n * z)⁻¹ := by rw [mul_inv_rev]
                  _ = ((z ^ (n + 1 : ℕ)) : ℂ)⁻¹ := by rw [pow_succ]
                  _ = z ^ (Int.negSucc n) := by rw [zpow_negSucc]
    _ = z ^ (Int.negSucc n) * ∑' m : ℤ, laurentTerm a m z := by
          refine congrArg (fun s : ℂ ↦ z ^ (Int.negSucc n) * s) ?_
          refine tsum_congr ?_
          intro m
          simp [laurentTerm]
    _ = ∑' m : ℤ, z ^ (Int.negSucc n) * laurentTerm a m z := by
          rw [tsum_mul_left]

/-- Helper for Proposition 3.1: after the direct Cauchy shift, a single Laurent term contributes
only when its exponent hits the residue value `-1`. -/
lemma circleIntegral_shifted_laurent_term_eq_residue
    {a : ℤ → ℂ} {R : ℝ} (hR : 0 < R) (n : ℕ) (m : ℤ) :
    (∮ z in C(0, R), z ^ (Int.negSucc n) * laurentTerm a m z) =
      if m = (n : ℤ) then (2 * Real.pi * Complex.I : ℂ) * a (n : ℤ) else 0 := by
  have hcongr :
      (∮ z in C(0, R), z ^ (Int.negSucc n) * laurentTerm a m z) =
        ∮ z in C(0, R), a m * z ^ (Int.negSucc n + m) := by
    refine circleIntegral.integral_congr hR.le ?_
    intro z hz
    have hz0 : z ≠ 0 := by
      have hzR : ‖z‖ = R := by
        simpa using mem_sphere_iff_norm.mp hz
      exact fun hz0 => (ne_of_gt hR) <| by
        have hnorm : ‖z‖ = 0 := by simpa [hz0]
        rw [hnorm] at hzR
        simpa using hzR.symm
    -- On the circle, the product of the shift and the Laurent monomial is one combined `zpow`.
    calc
      z ^ (Int.negSucc n) * laurentTerm a m z
        = z ^ (Int.negSucc n) * (a m * z ^ m) := by simp [laurentTerm]
      _ = a m * (z ^ (Int.negSucc n) * z ^ m) := by ac_rfl
      _ = a m * z ^ (Int.negSucc n + m) := by rw [zpow_add₀ hz0]
  calc
    (∮ z in C(0, R), z ^ (Int.negSucc n) * laurentTerm a m z)
      = ∮ z in C(0, R), a m * z ^ (Int.negSucc n + m) := hcongr
    _ = a m * (∮ z in C(0, R), z ^ (Int.negSucc n + m)) := by
          rw [circleIntegral.integral_const_mul]
    _ = a m * (if Int.negSucc n + m = -1 then 2 * Real.pi * Complex.I else 0) := by
          rw [circleIntegral_zpow_eq_residue hR]
    _ = if m = (n : ℤ) then (2 * Real.pi * Complex.I : ℂ) * a (n : ℤ) else 0 := by
          by_cases hm : m = (n : ℤ)
          · subst hm
            have hres : Int.negSucc n + (n : ℤ) = -1 := by
              omega
            simp [hres, mul_comm, mul_left_comm]
          · have hneq : Int.negSucc n + m ≠ -1 := by
              intro hres
              omega
            simp [hm, hneq]

/-- Helper for Proposition 3.1: the `n`th coefficient of the Cauchy power series on an
intermediate circle matches the `n`th nonnegative Laurent coefficient. -/
lemma cauchyPowerSeries_nonneg_coeff_apply_one
    {a : ℤ → ℂ} {ρ₂ ρ₁ R : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    (hρ₂R : ρ₂ < R) (hRρ₁ : R < ρ₁) (n : ℕ) :
    cauchyPowerSeries (fun z : ℂ ↦ ∑' m : ℤ, a m * z ^ m) 0 (R : ℝ) n (fun _ ↦ (1 : ℂ)) =
      a (n : ℤ) := by
  have hR0 : 0 < (R : ℝ) := by
    exact_mod_cast lt_of_le_of_lt ρ₂.2 hρ₂R
  have hsphere :
      sphere (0 : ℂ) (R : ℝ) ⊆ complexOpenAnnulus ρ₂ ρ₁ :=
    sphere_subset_complexOpenAnnulus_of_lt_lt (R := R) hρ₂R hRρ₁
  -- First rewrite the Cauchy coefficient integrand as the shifted Laurent series from the source
  -- proof.
  rw [cauchyPowerSeries_apply]
  simp only [sub_zero]
  calc
    (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z in C(0, (R : ℝ)),
          (1 / z) ^ n • z⁻¹ • (∑' m : ℤ, a m * z ^ m)
      = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ z in C(0, (R : ℝ)), ∑' m : ℤ, z ^ (Int.negSucc n) * laurentTerm a m z := by
            refine congrArg (fun w : ℂ ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ • w) ?_
            refine circleIntegral.integral_congr hR0.le ?_
            intro z hz
            have hzAnn : z ∈ complexOpenAnnulus ρ₂ ρ₁ := hsphere hz
            have hz0 : z ≠ 0 := by
              intro hz0
              have hzR : ‖z‖ = (R : ℝ) := by
                simpa using mem_sphere_iff_norm.mp hz
              have hzero : (0 : ℝ) = R := by simpa [hz0] using hzR
              exact (ne_of_gt hR0) hzero.symm
            simpa using cauchy_nonneg_integrand_eq_shifted_tsum
              (a := a) hz0 (ha.summable hzAnn) n
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∑' m : ℤ, ∮ z in C(0, (R : ℝ)), z ^ (Int.negSucc n) * laurentTerm a m z := by
            rw [circleIntegral_tsum_cauchy_nonneg_laurent_family
              (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) (R := R) ha hρ₂R hRρ₁ n]
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∑' m : ℤ, if m = (n : ℤ) then (2 * Real.pi * Complex.I : ℂ) * a (n : ℤ) else 0 := by
            refine congrArg (fun s : ℂ ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ • s) ?_
            refine tsum_congr ?_
            intro m
            exact circleIntegral_shifted_laurent_term_eq_residue (a := a) hR0 n m
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ((2 * Real.pi * Complex.I : ℂ) * a (n : ℤ)) := by
          rw [tsum_ite_eq]
    _ = a (n : ℤ) := by
          have htwo_pi_i_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
            simp [Real.pi_ne_zero]
          rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ htwo_pi_i_ne, one_mul]

/-- Helper for Proposition 3.1: the Cauchy power series on an intermediate circle is exactly the
formal scalar power series built from the nonnegative Laurent coefficients. -/
lemma cauchyPowerSeries_laurent_sum_eq_nonneg_coeff
    {a : ℤ → ℂ} {ρ₂ ρ₁ R : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    (hρ₂R : ρ₂ < R) (hRρ₁ : R < ρ₁) :
    cauchyPowerSeries (fun z : ℂ ↦ ∑' m : ℤ, a m * z ^ m) 0 (R : ℝ) =
      FormalMultilinearSeries.ofScalars ℂ (fun n : ℕ ↦ a (n : ℤ)) := by
  -- Once the coefficients agree at `1`, both multilinear series are the same termwise `mkPiRing`.
  ext n
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq
      (p := cauchyPowerSeries (fun z : ℂ ↦ ∑' m : ℤ, a m * z ^ m) 0 (R : ℝ))]
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq
      (p := FormalMultilinearSeries.ofScalars ℂ (fun k : ℕ ↦ a (k : ℤ)))]
  rw [FormalMultilinearSeries.coeff_ofScalars]
  -- Evaluating the `mkPiRing` maps at `1` recovers the scalar coefficient identity.
  have hcoeff :
      (cauchyPowerSeries (fun z : ℂ ↦ ∑' m : ℤ, a m * z ^ m) 0 (R : ℝ)).coeff n = a (n : ℤ) := by
    change
      cauchyPowerSeries (fun z : ℂ ↦ ∑' m : ℤ, a m * z ^ m) 0 (R : ℝ) n
          (fun _ ↦ (1 : ℂ)) = a (n : ℤ)
    exact cauchyPowerSeries_nonneg_coeff_apply_one
      (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) (R := R) ha hρ₂R hRρ₁ n
  exact congrArg (fun q : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ ℂ) ℂ ↦ q (fun _ ↦ (1 : ℂ)))
    (congrArg (ContinuousMultilinearMap.mkPiRing ℂ (Fin n)) hcoeff)

/-- Helper for Proposition 3.1: the reciprocal residue exponent `-(n + 2) - m` equals `-1`
exactly when the Laurent index is `Int.negSucc n`. -/
lemma reciprocal_residue_exponent_eq_neg_one_iff (n : ℕ) (m : ℤ) :
    (-(n + 2 : ℤ) - m = -1) ↔ m = Int.negSucc n := by
  omega

/-- Helper for Proposition 3.1: inversion carries the reciprocal-radius circle back to the
original radius-`r` circle. -/
lemma inv_mem_sphere_of_mem_reciprocal_sphere
    {r : NNReal} {w : ℂ}
    (hw : w ∈ sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ))) :
    w⁻¹ ∈ sphere (0 : ℂ) (r : ℝ) := by
  -- On the reciprocal circle we know `‖w‖ = r⁻¹`, so taking norms after inversion gives `‖w⁻¹‖ = r`.
  have hw' : ‖w‖ = (((r⁻¹ : NNReal) : ℝ)) := by
    simpa [sub_zero] using hw
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  rw [norm_inv, hw']
  simp [NNReal.coe_inv]

/-- Helper for Proposition 3.1: at a nonzero point, the reciprocal Cauchy integrand is exactly
the shifted Laurent `tsum` whose residue isolates the negative coefficient. -/
lemma reciprocal_cauchy_integrand_eq_shifted_tsum
    {a : ℤ → ℂ} {w : ℂ} (hw0 : w ≠ 0)
    (hsumw : Summable (fun m : ℤ ↦ a m * (w⁻¹) ^ m)) (n : ℕ) :
    (1 / w) ^ n • w⁻¹ • (w⁻¹ * ∑' m : ℤ, a m * (w⁻¹) ^ m) =
      ∑' m : ℤ, w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹) := by
  have hexp : Int.negSucc (n + 1) = (-(n + 2 : ℤ)) := by
    omega
  -- Rewrite the reciprocal Cauchy kernel as one fixed negative power, then push that fixed factor
  -- through the Laurent sum in the reciprocal variable.
  calc
    (1 / w) ^ n • w⁻¹ • (w⁻¹ * ∑' m : ℤ, a m * (w⁻¹) ^ m)
      = w ^ (-(n + 2 : ℤ)) * ∑' m : ℤ, a m * (w⁻¹) ^ m := by
          rw [smul_eq_mul, smul_eq_mul]
          calc
            (1 / w : ℂ) ^ n * (w⁻¹ * (w⁻¹ * ∑' m : ℤ, a m * (w⁻¹) ^ m))
              = (((1 / w : ℂ) ^ n) * (w⁻¹ * w⁻¹)) * ∑' m : ℤ, a m * (w⁻¹) ^ m := by
                  ring
            _ = w ^ (-(n + 2 : ℤ)) * ∑' m : ℤ, a m * (w⁻¹) ^ m := by
                  congr 1
                  calc
                    ((1 / w : ℂ) ^ n) * (w⁻¹ * w⁻¹)
                      = (w⁻¹) ^ n * (w⁻¹ * w⁻¹) := by simp [one_div]
                    _ = (w⁻¹) ^ n * (w⁻¹) ^ (2 : ℕ) := by rw [pow_two]
                    _ = (w⁻¹) ^ (n + 2 : ℕ) := by rw [← pow_add]
                    _ = ((w ^ (n + 2 : ℕ)) : ℂ)⁻¹ := by rw [inv_pow]
                    _ = w ^ (Int.negSucc (n + 1)) := by rw [zpow_negSucc]
                    _ = w ^ (-(n + 2 : ℤ)) := by rw [hexp]
    _ = w ^ (-(n + 2 : ℤ)) * ∑' m : ℤ, laurentTerm a m (w⁻¹) := by
          refine congrArg (fun s : ℂ ↦ w ^ (-(n + 2 : ℤ)) * s) ?_
          refine tsum_congr ?_
          intro m
          simp [laurentTerm]
    _ = ∑' m : ℤ, w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹) := by
          rw [tsum_mul_left]

/-- Helper for Proposition 3.1: composing the Laurent family with inversion on the reciprocal
circle preserves the uniform summability needed for the reciprocal coefficient computation. -/
lemma reciprocal_shifted_laurent_summableUniformlyOn_sphere
    {a : ℤ → ℂ} {ρ₂ ρ₁ r : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    (hρ₂r : ρ₂ < r) (hrρ₁ : r < ρ₁) (n : ℕ) :
    SummableUniformlyOn
      (fun m w ↦ w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹))
      (sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ))) := by
  let s : Set ℂ := sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ))
  have hr0 : 0 < (r : ℝ) := by
    exact_mod_cast lt_of_le_of_lt ρ₂.2 hρ₂r
  have hrinv0 : 0 < (((r⁻¹ : NNReal) : ℝ)) := by
    simpa [NNReal.coe_inv] using one_div_pos.mpr hr0
  have hmaps_annulus : Set.MapsTo (fun w : ℂ ↦ w⁻¹) s (complexOpenAnnulus ρ₂ ρ₁) := by
    -- Inversion sends the reciprocal circle to the original radius-`r` circle inside the annulus.
    intro w hw
    exact sphere_subset_complexOpenAnnulus_of_lt_lt (R := r) hρ₂r hrρ₁
      (inv_mem_sphere_of_mem_reciprocal_sphere (r := r) hw)
  have hcont_inv : ContinuousOn (fun w : ℂ ↦ w⁻¹) s := by
    -- The reciprocal circle avoids the origin, so inversion is continuous there.
    refine continuousOn_inv₀.mono ?_
    intro w hw
    exact ne_zero_of_mem_sphere_zero_of_pos hrinv0 hw
  have hbase :
      HasSumLocallyUniformlyOn (laurentTerm a) (fun z ↦ ∑' m : ℤ, laurentTerm a m z)
        (complexOpenAnnulus ρ₂ ρ₁) :=
    ha.hasSumLocallyUniformlyOn
  have hcomp :
      HasSumLocallyUniformlyOn
        (fun m w ↦ laurentTerm a m (w⁻¹))
        (fun w ↦ ∑' m : ℤ, laurentTerm a m (w⁻¹)) s :=
    hbase.comp (fun w : ℂ ↦ w⁻¹) hmaps_annulus hcont_inv
  have hsum_cont :
      ContinuousOn (fun w : ℂ ↦ ∑' m : ℤ, laurentTerm a m (w⁻¹)) s := by
    -- Compose the annulus Laurent sum with inversion on the reciprocal sphere.
    have hbase_cont :
        ContinuousOn (fun z : ℂ ↦ ∑' m : ℤ, laurentTerm a m z) (complexOpenAnnulus ρ₂ ρ₁) :=
      (laurent_sum_analyticOnNhd_complexOpenAnnulus (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) ha).continuousOn
    simpa only [Function.comp_apply] using hbase_cont.comp hcont_inv hmaps_annulus
  have hshift_cont : ContinuousOn (fun w : ℂ ↦ w ^ (-(n + 2 : ℤ))) s := by
    -- The fixed reciprocal shift is another continuous `zpow` on the nonzero circle.
    refine ((continuousOn_zpow₀ (m := (-(n + 2 : ℤ)))).mono ?_)
    intro w hw
    exact ne_zero_of_mem_sphere_zero_of_pos hrinv0 hw
  have hshifted :
      HasSumLocallyUniformlyOn
        (fun m w ↦ w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹))
        (fun w ↦ w ^ (-(n + 2 : ℤ)) * ∑' m : ℤ, laurentTerm a m (w⁻¹)) s :=
    hasSumLocallyUniformlyOn_mul_fixed hcomp hshift_cont hsum_cont
  have hscompact : IsCompact s := by
    simpa [s] using isCompact_sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ))
  have huniform :
      HasSumUniformlyOn
        (fun m w ↦ w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹))
        (fun w ↦ w ^ (-(n + 2 : ℤ)) * ∑' m : ℤ, laurentTerm a m (w⁻¹)) s :=
    hasSumUniformlyOn_of_hasSumLocallyUniformlyOn_isCompact hscompact hshifted
  -- The reciprocal sphere is compact, so the local-uniform reciprocal series becomes uniformly
  -- summable there.
  exact huniform.summableUniformlyOn

/-- Helper for Proposition 3.1: after composing the Laurent family with inversion and multiplying
by the fixed reciprocal shift, one may still integrate the series termwise on the reciprocal
circle. -/
lemma circleIntegral_tsum_reciprocal_laurent_family
    {a : ℤ → ℂ} {ρ₂ ρ₁ r : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    (hρ₂r : ρ₂ < r) (hrρ₁ : r < ρ₁) (n : ℕ) :
    (∮ w in C(0, (((r⁻¹ : NNReal) : ℝ))),
        ∑' m : ℤ, w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹)) =
      ∑' m : ℤ,
        ∮ w in C(0, (((r⁻¹ : NNReal) : ℝ))), w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹) := by
  let s : Set ℂ := sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ))
  have hr0 : 0 < (r : ℝ) := by
    exact_mod_cast lt_of_le_of_lt ρ₂.2 hρ₂r
  have hrinv0 : 0 < (r⁻¹ : NNReal) := inv_pos.mpr (lt_of_le_of_lt ρ₂.2 hρ₂r)
  have hrinv0_real : 0 < (((r⁻¹ : NNReal) : ℝ)) := by
    exact_mod_cast hrinv0
  have hcont_inv : ContinuousOn (fun w : ℂ ↦ w⁻¹) s := by
    refine continuousOn_inv₀.mono ?_
    intro w hw
    exact ne_zero_of_mem_sphere_zero_of_pos hrinv0_real hw
  have hmaps_sphere : Set.MapsTo (fun w : ℂ ↦ w⁻¹) s (sphere (0 : ℂ) (r : ℝ)) := by
    intro w hw
    exact inv_mem_sphere_of_mem_reciprocal_sphere (r := r) hw
  have hshifted :
      SummableUniformlyOn
        (fun m w ↦ w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹))
        s :=
    reciprocal_shifted_laurent_summableUniformlyOn_sphere
      (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) (r := r) ha hρ₂r hrρ₁ n
  -- The reciprocal family is continuous termwise on the reciprocal circle, so the uniform-sum
  -- circle-integral theorem applies directly.
  exact
    circleIntegral_tsum_of_summableUniformlyOn_sphere
      (R := r⁻¹)
      (F := fun m w ↦ w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹))
      (fun m ↦
        ((continuousOn_zpow₀ (m := (-(n + 2 : ℤ)))).mono fun w hw ↦
          ne_zero_of_mem_sphere_zero_of_pos hrinv0_real hw).mul
          ((laurentTerm_continuousOn_sphere (a := a) (R := r) hr0 m).comp hcont_inv
            hmaps_sphere))
      hshifted

/-- Helper for Proposition 3.1: on the reciprocal circle, a single shifted reciprocal Laurent term
contributes exactly when its exponent is the residue exponent `-1`. -/
lemma circleIntegral_reciprocal_shifted_laurent_term_eq_residue
    {a : ℤ → ℂ} {r : NNReal} (hr0 : 0 < (r : ℝ)) (n : ℕ) (m : ℤ) :
    (∮ w in C(0, (((r⁻¹ : NNReal) : ℝ))),
        w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹)) =
      if m = Int.negSucc n then (2 * Real.pi * Complex.I : ℂ) * a (Int.negSucc n) else 0 := by
  have hrinv0 : 0 < (((r⁻¹ : NNReal) : ℝ)) := by
    exact_mod_cast inv_pos.mpr hr0
  have hcongr :
      (∮ w in C(0, (((r⁻¹ : NNReal) : ℝ))),
          w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹)) =
        ∮ w in C(0, (((r⁻¹ : NNReal) : ℝ))), a m * w ^ (-(n + 2 : ℤ) - m) := by
    refine circleIntegral.integral_congr hrinv0.le ?_
    intro w hw
    have hw0 : w ≠ 0 := ne_zero_of_mem_sphere_zero_of_pos hrinv0 hw
    -- On the reciprocal circle, the fixed reciprocal shift and the Laurent monomial collapse to
    -- one combined `zpow`.
    calc
      w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹)
        = w ^ (-(n + 2 : ℤ)) * (a m * (w⁻¹) ^ m) := by simp [laurentTerm]
      _ = a m * (w ^ (-(n + 2 : ℤ)) * (w⁻¹) ^ m) := by ac_rfl
      _ = a m * (w ^ (-(n + 2 : ℤ)) * (w ^ m)⁻¹) := by rw [inv_zpow]
      _ = a m * (w ^ (-(n + 2 : ℤ)) * w ^ (-m)) := by rw [← zpow_neg]
      _ = a m * w ^ (-(n + 2 : ℤ) + -m) := by rw [zpow_add₀ hw0]
      _ = a m * w ^ (-(n + 2 : ℤ) - m) := by simp [sub_eq_add_neg]
  calc
    (∮ w in C(0, (((r⁻¹ : NNReal) : ℝ))),
        w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹))
      = ∮ w in C(0, (((r⁻¹ : NNReal) : ℝ))), a m * w ^ (-(n + 2 : ℤ) - m) := hcongr
    _ = a m * (∮ w in C(0, (((r⁻¹ : NNReal) : ℝ))), w ^ (-(n + 2 : ℤ) - m)) := by
          rw [circleIntegral.integral_const_mul]
    _ = a m * (if (-(n + 2 : ℤ) - m = -1) then 2 * Real.pi * Complex.I else 0) := by
          rw [circleIntegral_zpow_eq_residue hrinv0]
    _ = if m = Int.negSucc n then (2 * Real.pi * Complex.I : ℂ) * a (Int.negSucc n) else 0 := by
          by_cases hm : m = Int.negSucc n
          · subst hm
            have hres : (-(n + 2 : ℤ) - Int.negSucc n = -1) := by
              omega
            rw [if_pos hres, if_pos rfl]
            ring
          · have hneq : (-(n + 2 : ℤ) - m ≠ -1) := by
              intro hres
              exact hm ((reciprocal_residue_exponent_eq_neg_one_iff n m).mp hres)
            rw [if_neg hneq, if_neg hm]
            simp

/-- Helper for Proposition 3.1: the `n`th coefficient of the reciprocal-variable Cauchy power
series matches the `n`th negative Laurent coefficient. -/
lemma reciprocal_cauchyPowerSeries_neg_coeff_apply_one
    {a : ℤ → ℂ} {ρ₂ ρ₁ r : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    (hρ₂r : ρ₂ < r) (hrρ₁ : r < ρ₁) (n : ℕ) :
    cauchyPowerSeries
        (fun w : ℂ ↦ (w⁻¹) * ∑' m : ℤ, a m * (w⁻¹) ^ m)
        0 ((r⁻¹ : NNReal) : ℝ) n (fun _ ↦ (1 : ℂ)) =
      a (Int.negSucc n) := by
  -- Route correction: the previous reciprocal integrand used an extra leading minus sign, which
  -- flipped the target coefficient. The corrected integrand should now return the Laurent
  -- coefficient with the expected sign.
  have hr0 : 0 < (r : ℝ) := by
    exact_mod_cast lt_of_le_of_lt ρ₂.2 hρ₂r
  have hsphere :
      sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ)) ⊆
        {w : ℂ | w⁻¹ ∈ complexOpenAnnulus ρ₂ ρ₁} := by
    intro w hw
    exact sphere_subset_complexOpenAnnulus_of_lt_lt (R := r) hρ₂r hrρ₁
      (inv_mem_sphere_of_mem_reciprocal_sphere (r := r) hw)
  rw [cauchyPowerSeries_apply]
  simp only [sub_zero]
  calc
    (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ w in C(0, (((r⁻¹ : NNReal) : ℝ))),
          (1 / w) ^ n • w⁻¹ • ((w⁻¹) * ∑' m : ℤ, a m * (w⁻¹) ^ m)
      = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ w in C(0, (((r⁻¹ : NNReal) : ℝ))),
            ∑' m : ℤ, w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹) := by
              refine congrArg (fun s : ℂ ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ • s) ?_
              refine circleIntegral.integral_congr (show 0 ≤ (((r⁻¹ : NNReal) : ℝ)) by positivity) ?_
              intro w hw
              have hwAnn : w⁻¹ ∈ complexOpenAnnulus ρ₂ ρ₁ := hsphere hw
              have hw0 : w ≠ 0 := by
                have hrinv0 : 0 < (((r⁻¹ : NNReal) : ℝ)) := by
                  exact_mod_cast inv_pos.mpr hr0
                exact ne_zero_of_mem_sphere_zero_of_pos hrinv0 hw
              simpa using reciprocal_cauchy_integrand_eq_shifted_tsum
                (a := a) hw0 (ha.summable hwAnn) n
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∑' m : ℤ,
            ∮ w in C(0, (((r⁻¹ : NNReal) : ℝ))),
              w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹) := by
            rw [circleIntegral_tsum_reciprocal_laurent_family
              (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) (r := r) ha hρ₂r hrρ₁ n]
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∑' m : ℤ,
            if m = Int.negSucc n then (2 * Real.pi * Complex.I : ℂ) * a (Int.negSucc n) else 0 := by
            refine congrArg (fun s : ℂ ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ • s) ?_
            refine tsum_congr ?_
            intro m
            exact circleIntegral_reciprocal_shifted_laurent_term_eq_residue (a := a) hr0 n m
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ((2 * Real.pi * Complex.I : ℂ) * a (Int.negSucc n)) := by
          rw [tsum_ite_eq]
    _ = a (Int.negSucc n) := by
          have htwo_pi_i_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
            simp [Real.pi_ne_zero]
          rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ htwo_pi_i_ne, one_mul]

/-- Helper for Proposition 3.1: the reciprocal-variable Cauchy power series is exactly the formal
scalar power series built from the negative Laurent coefficients. -/
lemma reciprocal_cauchyPowerSeries_eq_neg_coeff
    {a : ℤ → ℂ} {ρ₂ ρ₁ r : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    (hρ₂r : ρ₂ < r) (hrρ₁ : r < ρ₁) :
    cauchyPowerSeries
        (fun w : ℂ ↦ (w⁻¹) * ∑' m : ℤ, a m * (w⁻¹) ^ m)
        0 ((r⁻¹ : NNReal) : ℝ) =
      FormalMultilinearSeries.ofScalars ℂ (fun n : ℕ ↦ a (Int.negSucc n)) := by
  -- As on the inner branch, the whole formal-series equality is a wrapper around coefficientwise
  -- equality at `1`.
  ext n
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq
      (p := cauchyPowerSeries
        (fun w : ℂ ↦ (w⁻¹) * ∑' m : ℤ, a m * (w⁻¹) ^ m)
        0 ((r⁻¹ : NNReal) : ℝ))]
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq
      (p := FormalMultilinearSeries.ofScalars ℂ (fun k : ℕ ↦ a (Int.negSucc k)))]
  rw [FormalMultilinearSeries.coeff_ofScalars]
  -- The reciprocal wrapper likewise collapses to the scalar coefficient identity at `1`.
  have hcoeff :
      (cauchyPowerSeries
        (fun w : ℂ ↦ (w⁻¹) * ∑' m : ℤ, a m * (w⁻¹) ^ m)
        0 ((r⁻¹ : NNReal) : ℝ)).coeff n = a (Int.negSucc n) := by
    change
      cauchyPowerSeries
          (fun w : ℂ ↦ (w⁻¹) * ∑' m : ℤ, a m * (w⁻¹) ^ m)
          0 ((r⁻¹ : NNReal) : ℝ) n (fun _ ↦ (1 : ℂ)) = a (Int.negSucc n)
    exact reciprocal_cauchyPowerSeries_neg_coeff_apply_one
      (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) (r := r) ha hρ₂r hrρ₁ n
  exact congrArg (fun q : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ ℂ) ℂ ↦ q (fun _ ↦ (1 : ℂ)))
    (congrArg (ContinuousMultilinearMap.mkPiRing ℂ (Fin n)) hcoeff)

/-- Helper for Proposition 3.1: the nonnegative Laurent tail is the analytic branch that should
extend from the annulus across the origin to the whole disc `‖z‖ < ρ₁`. -/
lemma laurent_nonneg_part_analyticOnNhd
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} (hρ : ρ₂ < ρ₁) (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∑' n : ℕ, a (n : ℤ) * z ^ n) (ball (0 : ℂ) ρ₁) := by
  -- Route correction: `hρ` rules out the vacuous empty-annulus case, so the remaining work is to
  -- identify the Cauchy power series on each
  -- intermediate circle with the nonnegative Laurent coefficients, then transfer analyticity
  -- from that circle integral model to the whole smaller disc.
  intro z hz
  -- Choose an intermediate circle that contains `z` and still stays inside the annulus.
  rcases exists_intermediate_radius_for_ball_point hρ hz with ⟨R, hRmid, hRρ₁⟩
  have hρ₂R : ρ₂ < R := lt_of_le_of_lt (le_max_left _ _) hRmid
  have hzR : ‖z‖₊ < R := lt_of_le_of_lt (le_max_right _ _) hRmid
  have hzballR : z ∈ ball (0 : ℂ) (R : ℝ) := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hzR
  let F : ℂ → ℂ := fun w ↦ ∑' m : ℤ, a m * w ^ m
  have hcircle : CircleIntegrable F 0 (R : ℝ) :=
    laurent_sum_circleIntegrable (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) (R := R) ha hρ₂R hRρ₁
  have hR0 : 0 < R := lt_of_le_of_lt ρ₂.2 hρ₂R
  have hseries :
      cauchyPowerSeries F 0 (R : ℝ) =
        FormalMultilinearSeries.ofScalars ℂ (fun n : ℕ ↦ a (n : ℤ)) :=
    cauchyPowerSeries_laurent_sum_eq_nonneg_coeff (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) (R := R)
      ha hρ₂R hRρ₁
  have hpower :
      HasFPowerSeriesOnBall (circleInnerPiece F R)
        (FormalMultilinearSeries.ofScalars ℂ (fun n : ℕ ↦ a (n : ℤ))) 0 R := by
    -- Rewrite the local Cauchy model to the formal scalar series with coefficients `a n`.
    have hbase :
        HasFPowerSeriesOnBall
          (fun w ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ t in C(0, (R : ℝ)), (t - w)⁻¹ • F t)
          (cauchyPowerSeries F 0 (R : ℝ)) 0 R :=
      hasFPowerSeriesOn_cauchy_integral (c := (0 : ℂ)) (R := R) hcircle hR0
    have hbase' :
        HasFPowerSeriesOnBall (circleInnerPiece F R) (cauchyPowerSeries F 0 (R : ℝ)) 0 R := by
      convert hbase using 1
    simpa [hseries] using hbase'
  have hEqOnBall :
      Set.EqOn (circleInnerPiece F R) (fun w : ℂ ↦ ∑' n : ℕ, a (n : ℤ) * w ^ n)
        (ball (0 : ℂ) (R : ℝ)) := by
    -- The power-series witness evaluates to the scalar `tsum` of the nonnegative Laurent tail.
    intro w hw
    have hweball : w ∈ Metric.eball (0 : ℂ) R := by
      simpa [Metric.mem_eball, edist_eq_enorm_sub, sub_zero] using hw
    have hsum :
        HasSum (fun n : ℕ ↦ a (n : ℤ) * w ^ n) (circleInnerPiece F R w) := by
      simpa [sub_zero, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using
        hpower.hasSum_sub hweball
    exact hsum.tsum_eq.symm
  have hzeballR : z ∈ Metric.eball (0 : ℂ) R := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub, sub_zero] using hzballR
  have hanalytic_circle : AnalyticAt ℂ (circleInnerPiece F R) z :=
    hpower.analyticAt_of_mem hzeballR
  have hNearEq :
      circleInnerPiece F R =ᶠ[𝓝 z] (fun w : ℂ ↦ ∑' n : ℕ, a (n : ℤ) * w ^ n) := by
    -- The equality on the full smaller ball upgrades to eventual equality near the chosen point.
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨ball (0 : ℂ) (R : ℝ), Metric.isOpen_ball.mem_nhds hzballR, hEqOnBall⟩
  exact hanalytic_circle.congr hNearEq

/-- Helper for Proposition 3.1: the negative Laurent tail is the analytic branch that should
extend from the annulus to the full exterior `ρ₂ < ‖z‖` by passing to the reciprocal variable. -/
lemma laurent_neg_part_analyticOnNhd
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} (hρ : ρ₂ < ρ₁) (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n))
      (closedBall (0 : ℂ) ρ₂)ᶜ := by
  -- Route correction: `hρ` removes the vacuous empty-annulus case, and the outer branch should
  -- be rewritten in the reciprocal variable `w = z⁻¹`,
  -- and the remaining blocker is the corresponding Cauchy-power-series coefficient identity for
  -- the reciprocal-variable circle integral on radii `ρ₂ < r`.
  intro z hz
  -- Choose an intermediate inner circle whose radius is still smaller than `‖z‖`.
  rcases exists_intermediate_radius_for_exterior_point_lt_upper hρ hz with ⟨r, hρ₂r, hrρ₁, hrz⟩
  have hz_nonzero : z ≠ 0 := by
    intro hz0
    have : z ∈ closedBall (0 : ℂ) (ρ₂ : ℝ) := by
      simpa [hz0, Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hz this
  have hzinv_ball : z⁻¹ ∈ ball (0 : ℂ) ((r : ℝ)⁻¹) := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have hrz' : (r : ℝ) < ‖z‖ := by exact_mod_cast hrz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz_nonzero
    have hrpos : 0 < (r : ℝ) := by
      exact_mod_cast lt_of_le_of_lt ρ₂.2 hρ₂r
    rw [norm_inv]
    simpa [one_div] using (one_div_lt_one_div hzpos hrpos).2 hrz'
  let F : ℂ → ℂ := fun w ↦ w⁻¹ * ∑' m : ℤ, a m * (w⁻¹) ^ m
  let G : ℂ → ℂ := fun w ↦ ∑' n : ℕ, a (Int.negSucc n) * w ^ n
  let C : ℂ → ℂ :=
    fun w ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ t in C(0, (((r⁻¹ : NNReal) : ℝ))), (t - w)⁻¹ • F t
  have hr0 : 0 < r := lt_of_le_of_lt ρ₂.2 hρ₂r
  have hr0_real : 0 < (r : ℝ) := by exact_mod_cast hr0
  have hrinv0 : 0 < (r⁻¹ : NNReal) := inv_pos.mpr hr0
  have hrinv0_real : 0 < (((r⁻¹ : NNReal) : ℝ)) := by exact_mod_cast hrinv0
  have hsphere_inv :
      Set.MapsTo (fun w : ℂ ↦ w⁻¹) (sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ)))
        (sphere (0 : ℂ) (r : ℝ)) := by
    intro w hw
    exact inv_mem_sphere_of_mem_reciprocal_sphere (r := r) hw
  have hsphere_annulus :
      Set.MapsTo (fun w : ℂ ↦ w⁻¹) (sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ)))
        (complexOpenAnnulus ρ₂ ρ₁) := by
    intro w hw
    exact sphere_subset_complexOpenAnnulus_of_lt_lt (R := r) hρ₂r hrρ₁ (hsphere_inv hw)
  have hcont_inv :
      ContinuousOn (fun w : ℂ ↦ w⁻¹) (sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ))) := by
    refine continuousOn_inv₀.mono ?_
    intro w hw
    exact ne_zero_of_mem_sphere_zero_of_pos hrinv0_real hw
  have hcont_sum_inv :
      ContinuousOn (fun w : ℂ ↦ ∑' m : ℤ, a m * (w⁻¹) ^ m)
        (sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ))) := by
    -- Compose the annulus Laurent sum with inversion on the reciprocal circle.
    have hcomp :
        ContinuousOn
          ((fun u : ℂ ↦ ∑' m : ℤ, a m * u ^ m) ∘ fun w : ℂ ↦ w⁻¹)
          (sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ))) :=
      (laurent_sum_analyticOnNhd_complexOpenAnnulus (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) ha).continuousOn.comp
        hcont_inv hsphere_annulus
    simpa only [Function.comp_apply] using hcomp
  have hcont_F :
      ContinuousOn F (sphere (0 : ℂ) (((r⁻¹ : NNReal) : ℝ))) := by
    -- The reciprocal integrand is the product of the analytic inverse factor and the pulled-back
    -- Laurent sum.
    exact hcont_inv.mul hcont_sum_inv
  have hcircle : CircleIntegrable F 0 (((r⁻¹ : NNReal) : ℝ)) :=
    hcont_F.circleIntegrable (r⁻¹).2
  have hseries :
      cauchyPowerSeries F 0 (((r⁻¹ : NNReal) : ℝ)) =
        FormalMultilinearSeries.ofScalars ℂ (fun n : ℕ ↦ a (Int.negSucc n)) :=
    reciprocal_cauchyPowerSeries_eq_neg_coeff
      (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) (r := r) ha hρ₂r hrρ₁
  have hpower :
      HasFPowerSeriesOnBall C
        (FormalMultilinearSeries.ofScalars ℂ (fun n : ℕ ↦ a (Int.negSucc n))) 0 (r⁻¹ : NNReal) := by
    -- Rewrite the reciprocal Cauchy model to the formal scalar series with coefficients
    -- `a (Int.negSucc n)`.
    have hbase :
        HasFPowerSeriesOnBall C
          (cauchyPowerSeries F 0 (((r⁻¹ : NNReal) : ℝ))) 0 (r⁻¹ : NNReal) := by
      simpa [C, F] using
        (hasFPowerSeriesOn_cauchy_integral (c := (0 : ℂ)) (R := r⁻¹) hcircle hrinv0)
    rw [hseries] at hbase
    exact hbase
  have hEqOnBall :
      Set.EqOn C G (ball (0 : ℂ) (((r⁻¹ : NNReal) : ℝ))) := by
    -- The power-series witness evaluates to the scalar `tsum` of the negative Laurent
    -- coefficients in the reciprocal variable.
    intro w hw
    have hweball : w ∈ Metric.eball (0 : ℂ) (r⁻¹ : NNReal) := by
      simpa [Metric.mem_eball, edist_eq_enorm_sub, sub_zero] using hw
    have hsum :
        HasSum (fun n : ℕ ↦ a (Int.negSucc n) * w ^ n) (C w) := by
      simpa [C, G, sub_zero, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using
        hpower.hasSum_sub hweball
    exact hsum.tsum_eq.symm
  have hzinv_eball : z⁻¹ ∈ Metric.eball (0 : ℂ) (r⁻¹ : NNReal) := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, NNReal.coe_inv, one_div] using hzinv_ball
  have hanalytic_C : AnalyticAt ℂ C (z⁻¹) :=
    hpower.analyticAt_of_mem hzinv_eball
  have hNearEq_CG : C =ᶠ[𝓝 z⁻¹] G := by
    -- Equality on the reciprocal ball upgrades to eventual equality near `z⁻¹`.
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨ball (0 : ℂ) (((r⁻¹ : NNReal) : ℝ)),
        Metric.isOpen_ball.mem_nhds hzinv_ball, hEqOnBall⟩
  have hanalytic_G : AnalyticAt ℂ G (z⁻¹) :=
    hanalytic_C.congr hNearEq_CG
  have hanalytic_inv : AnalyticAt ℂ (fun w : ℂ ↦ w⁻¹) z :=
    analyticAt_inv hz_nonzero
  have hanalytic_outer_model :
      AnalyticAt ℂ (fun w : ℂ ↦ w⁻¹ * G (w⁻¹)) z := by
    -- Compose the reciprocal-disc power series with inversion, then multiply by the outer `w⁻¹`
    -- factor from the Laurent-tail formula.
    exact hanalytic_inv.mul (hanalytic_G.comp hanalytic_inv)
  have hNearEq_outer :
      (fun w : ℂ ↦ w⁻¹ * G (w⁻¹)) =ᶠ[𝓝 z]
        (fun w : ℂ ↦ ∑' n : ℕ, a (Int.negSucc n) * w ^ (Int.negSucc n)) := by
    -- Near a nonzero point, the negative Laurent tail is exactly `w⁻¹` times the reciprocal power
    -- series.
    refine Filter.mem_of_superset (isOpen_ne.mem_nhds hz_nonzero) ?_
    intro w hw
    simpa [G] using (laurent_neg_part_eq_inv_mul_powerSeries (a := a) hw).symm
  exact hanalytic_outer_model.congr hNearEq_outer

/-- A Laurent expansion on an annulus yields the corresponding holomorphic decomposition into its
nonnegative and negative powers. -/
theorem HasLaurentExpansionOnAnnulus.exists_holomorphicAnnulusDecomposition
    {ρ₂ ρ₁ : NNReal} {f : ℂ → ℂ} (hf : HasLaurentExpansionOnAnnulus f ρ₂ ρ₁) :
    ∃ inner outer : ℂ → ℂ,
      AnalyticOnNhd ℂ inner (ball (0 : ℂ) ρ₁) ∧
        AnalyticOnNhd ℂ outer (closedBall (0 : ℂ) ρ₂)ᶜ ∧
        Set.EqOn f (fun z ↦ inner z + outer z) (complexOpenAnnulus ρ₂ ρ₁) := by
  by_cases hρ : ρ₂ < ρ₁
  · rcases hf with ⟨a, ha, hEq⟩
    let inner : ℂ → ℂ := fun z ↦ ∑' n : ℕ, a (n : ℤ) * z ^ n
    let outer : ℂ → ℂ := fun z ↦ ∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n)
    refine ⟨inner, outer, ?_, ?_, ?_⟩
    · -- Route correction: the owner proof now follows the textbook Laurent-tail split.
      simpa [inner] using
        laurent_nonneg_part_analyticOnNhd (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) hρ ha
    · -- TODO: rewrite `outer` using `laurent_neg_part_eq_inv_mul_powerSeries`, prove the
      -- reciprocal power series is analytic on the disc `‖w‖ < ρ₂⁻¹`, and transport that
      -- analyticity across inversion to the exterior `(closedBall 0 ρ₂)ᶜ`.
      simpa [outer] using
        laurent_neg_part_analyticOnNhd (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) hρ ha
    · -- The annulus equality is the direct `ℤ = ℕ ⊕ negSucc ℕ` reindexing of the Laurent sum.
      simpa [inner, outer] using laurent_split_eqOn_annulus (a := a) (ρ₂ := ρ₂) (ρ₁ := ρ₁) ha hEq
  · refine ⟨fun _ ↦ 0, fun _ ↦ 0, ?_, ?_, ?_⟩
    · -- The zero function is analytic on every disc.
      simpa using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ ↦ (0 : ℂ)) (ball (0 : ℂ) ρ₁))
    · -- The zero function is analytic on every exterior region.
      simpa using
        (analyticOnNhd_const :
          AnalyticOnNhd ℂ (fun _ : ℂ ↦ (0 : ℂ)) (closedBall (0 : ℂ) ρ₂)ᶜ)
    · -- If the annulus is empty, the equality-on-annulus goal is vacuous.
      intro z hz
      exfalso
      have hz' : (ρ₂ : ENNReal) < ‖z‖₊ ∧ ‖z‖₊ < (ρ₁ : ENNReal) := by
        simpa [complexOpenAnnulus] using hz
      exact hρ (by exact_mod_cast lt_trans hz'.1 hz'.2)

/-- Helper for Proposition 3.1: an analytic function on an annulus admits a decomposition into an
inner holomorphic term on the disc and an outer holomorphic term on the exterior. -/
theorem analytic_exists_holomorphic_annulus_decomposition
    {ρ₂ ρ₁ : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁)) :
    ∃ inner outer : ℂ → ℂ,
      AnalyticOnNhd ℂ inner (ball (0 : ℂ) ρ₁) ∧
        AnalyticOnNhd ℂ outer (closedBall (0 : ℂ) ρ₂)ᶜ ∧
        Set.EqOn f (fun z ↦ inner z + outer z) (complexOpenAnnulus ρ₂ ρ₁) := by
  -- Route correction: the analytic-input statement is now the direct Laurent-expansion corollary
  -- of the owner theorem `HasLaurentExpansionOnAnnulus.exists_holomorphicAnnulusDecomposition`.
  simpa using hf.hasLaurentExpansionOnAnnulus.exists_holomorphicAnnulusDecomposition

/-- Helper for Proposition 3.1: a point that lies both in the disc `‖z‖ < ρ₁` and in the exterior
`ρ₂ < ‖z‖` lies in the overlap annulus. -/
lemma mem_complexOpenAnnulus_of_mem_ball_of_mem_exterior
    {ρ₂ ρ₁ : NNReal} {z : ℂ}
    (hzball : z ∈ ball (0 : ℂ) ρ₁) (hzext : z ∈ (closedBall (0 : ℂ) ρ₂)ᶜ) :
    z ∈ complexOpenAnnulus ρ₂ ρ₁ := by
  -- Translate the metric conditions into the two strict norm inequalities defining the annulus.
  have hzlt : ‖z‖ < ρ₁ := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hzball
  have hzgt : ρ₂ < ‖z‖ := by
    have hznot : ¬ ‖z‖ ≤ ρ₂ := by
      simpa [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero] using hzext
    exact lt_of_not_ge hznot
  change (ρ₂ : ENNReal) < ‖z‖₊ ∧ ‖z‖₊ < (ρ₁ : ENNReal)
  exact ⟨by exact_mod_cast hzgt, by exact_mod_cast hzlt⟩

/-- Helper for Proposition 3.1: if two analytic pieces agree on the overlap annulus, then the
piecewise function defined by the inner piece on the disc and the outer piece on the exterior is
entire. -/
lemma analyticOnNhd_piecewise_ball_exterior
    {ρ₂ ρ₁ : NNReal} (hρ : ρ₂ < ρ₁) {u v : ℂ → ℂ}
    [DecidablePred (· ∈ ball (0 : ℂ) ρ₁)]
    (hu : AnalyticOnNhd ℂ u (ball (0 : ℂ) ρ₁))
    (hv : AnalyticOnNhd ℂ v (closedBall (0 : ℂ) ρ₂)ᶜ)
    (hEq : Set.EqOn u v (complexOpenAnnulus ρ₂ ρ₁)) :
    AnalyticOnNhd ℂ (Set.piecewise (ball (0 : ℂ) ρ₁) u v) Set.univ := by
  classical
  intro z hz
  by_cases hzball : z ∈ ball (0 : ℂ) ρ₁
  · -- Inside the disc, the glued function is eventually just the inner branch.
    have hball : ball (0 : ℂ) ρ₁ ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds hzball
    have hNear : Set.piecewise (ball (0 : ℂ) ρ₁) u v =ᶠ[𝓝 z] u := by
      filter_upwards [hball] with w hw
      rw [Set.piecewise_eq_of_mem _ _ _ hw]
    exact (hu z hzball).congr hNear.symm
  · have hzext : z ∈ (closedBall (0 : ℂ) ρ₂)ᶜ := by
      rw [Set.mem_compl_iff]
      intro hzin
      apply hzball
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      have hzle : ‖z‖ ≤ ρ₂ := by
        simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hzin
      exact lt_of_le_of_lt hzle hρ
    -- On the exterior neighborhood, points that fall back into the disc lie in the overlap
    -- annulus, so the two branches agree there as well.
    have hext : (closedBall (0 : ℂ) ρ₂)ᶜ ∈ 𝓝 z :=
      Metric.isClosed_closedBall.isOpen_compl.mem_nhds hzext
    have hNear : Set.piecewise (ball (0 : ℂ) ρ₁) u v =ᶠ[𝓝 z] v := by
      filter_upwards [hext] with w hwext
      by_cases hwball : w ∈ ball (0 : ℂ) ρ₁
      · have hwann : w ∈ complexOpenAnnulus ρ₂ ρ₁ :=
          mem_complexOpenAnnulus_of_mem_ball_of_mem_exterior hwball hwext
        rw [Set.piecewise_eq_of_mem _ _ _ hwball, hEq hwann]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hwball]
    exact (hv z hzext).congr hNear.symm

/-- Proposition 3.1 (1): every holomorphic function on the annulus `ρ₂ < ‖z‖ < ρ₁` admits a
decomposition into a holomorphic function on `‖z‖ < ρ₁` and a holomorphic function on
`ρ₂ < ‖z‖`. -/
theorem exists_holomorphic_annulus_decomposition
    {ρ₂ ρ₁ : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁)) :
    ∃ inner outer : ℂ → ℂ,
      AnalyticOnNhd ℂ inner (ball (0 : ℂ) ρ₁) ∧
        AnalyticOnNhd ℂ outer (closedBall (0 : ℂ) ρ₂)ᶜ ∧
        Set.EqOn f (fun z ↦ inner z + outer z) (complexOpenAnnulus ρ₂ ρ₁) := by
  simpa using hf.hasLaurentExpansionOnAnnulus.exists_holomorphicAnnulusDecomposition

/-- Proposition 3.1 (2): such a decomposition is unique when the outer term tends to `0` at
infinity. -/
theorem holomorphic_annulus_decomposition_unique
    {ρ₂ ρ₁ : NNReal} (hρ : ρ₂ < ρ₁) {f₁ f₂ g₁ g₂ : ℂ → ℂ}
    (hf₁ : AnalyticOnNhd ℂ f₁ (ball (0 : ℂ) ρ₁))
    (hf₂ : AnalyticOnNhd ℂ f₂ (closedBall (0 : ℂ) ρ₂)ᶜ)
    (hg₁ : AnalyticOnNhd ℂ g₁ (ball (0 : ℂ) ρ₁))
    (hg₂ : AnalyticOnNhd ℂ g₂ (closedBall (0 : ℂ) ρ₂)ᶜ)
    (hdecomp :
      Set.EqOn (fun z ↦ f₁ z + f₂ z) (fun z ↦ g₁ z + g₂ z) (complexOpenAnnulus ρ₂ ρ₁))
    (hf₂_zero : Filter.Tendsto f₂ (Filter.cocompact ℂ) (𝓝 0))
    (hg₂_zero : Filter.Tendsto g₂ (Filter.cocompact ℂ) (𝓝 0)) :
    Set.EqOn f₁ g₁ (ball (0 : ℂ) ρ₁) ∧
      Set.EqOn f₂ g₂ (closedBall (0 : ℂ) ρ₂)ᶜ := by
  classical
  -- First rewrite the two decompositions as equality of the corresponding differences.
  have hdiff :
      Set.EqOn (fun z ↦ f₁ z - g₁ z) (fun z ↦ g₂ z - f₂ z) (complexOpenAnnulus ρ₂ ρ₁) := by
    intro z hz
    have hzsum := hdecomp hz
    have hzdiff := congrArg (fun w : ℂ => w - g₁ z - f₂ z) hzsum
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hzdiff
  let h : ℂ → ℂ :=
    Set.piecewise (ball (0 : ℂ) ρ₁) (fun z ↦ f₁ z - g₁ z) (fun z ↦ g₂ z - f₂ z)
  -- Glue the two differences into one entire function.
  have hh_analytic : AnalyticOnNhd ℂ h Set.univ := by
    simpa [h] using
      analyticOnNhd_piecewise_ball_exterior hρ (hf₁.sub hg₁) (hg₂.sub hf₂) hdiff
  -- Outside a large closed ball the glued function is literally the outer difference.
  have h_outer_eq : h =ᶠ[Filter.cocompact ℂ] fun z ↦ g₂ z - f₂ z := by
    have houtside : {z : ℂ | z ∉ closedBall (0 : ℂ) ρ₁} ∈ Filter.cocompact ℂ := by
      exact (Filter.mem_cocompact).2
        ⟨closedBall (0 : ℂ) ρ₁, isCompact_closedBall (0 : ℂ) ρ₁, by
          intro z hz
          exact hz⟩
    filter_upwards [houtside] with z hz
    have hzball : z ∉ ball (0 : ℂ) ρ₁ := by
      intro hzball
      apply hz
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      have hzlt : ‖z‖ < ρ₁ := by
        simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hzball
      exact hzlt.le
    change
      Set.piecewise (ball (0 : ℂ) ρ₁) (fun w ↦ f₁ w - g₁ w) (fun w ↦ g₂ w - f₂ w) z =
        (g₂ z - f₂ z)
    rw [Set.piecewise_eq_of_notMem _ _ _ hzball]
  have hh_tendsto : Filter.Tendsto h (Filter.cocompact ℂ) (𝓝 0) := by
    -- The outer difference tends to `0` at infinity, so the glued entire function does as well.
    have h_outer_zero : Filter.Tendsto (fun z ↦ g₂ z - f₂ z) (Filter.cocompact ℂ) (𝓝 0) := by
      simpa using hg₂_zero.sub hf₂_zero
    exact Filter.Tendsto.congr' h_outer_eq.symm h_outer_zero
  have hh_diff : Differentiable ℂ h :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mp hh_analytic)
  have hh_zero : h = Function.const ℂ 0 :=
    hh_diff.eq_const_of_tendsto_cocompact hh_tendsto
  have hf₁_eq : Set.EqOn f₁ g₁ (ball (0 : ℂ) ρ₁) := by
    intro z hz
    -- On the disc the glued function is `f₁ - g₁`, hence the difference vanishes.
    have hz_zero : h z = 0 := by
      simpa using congrFun hh_zero z
    have hz_diff : f₁ z - g₁ z = 0 := by
      simpa [h, Set.piecewise_eq_of_mem, hz] using hz_zero
    exact sub_eq_zero.mp hz_diff
  have hf₂_eq : Set.EqOn f₂ g₂ (closedBall (0 : ℂ) ρ₂)ᶜ := by
    intro z hzext
    by_cases hzball : z ∈ ball (0 : ℂ) ρ₁
    · -- On the overlap annulus, the decomposition equality transfers the already proved inner
      -- equality to the outer equality.
      have hzann : z ∈ complexOpenAnnulus ρ₂ ρ₁ :=
        mem_complexOpenAnnulus_of_mem_ball_of_mem_exterior hzball hzext
      have hzsum := hdecomp hzann
      have hinner : f₁ z = g₁ z := hf₁_eq hzball
      have hzsum' : g₁ z + f₂ z = g₁ z + g₂ z := by
        simpa [hinner] using hzsum
      exact add_left_cancel hzsum'
    · -- Outside the outer disc the glued function is `g₂ - f₂`, so this difference vanishes too.
      have hz_zero : h z = 0 := by
        simpa using congrFun hh_zero z
      have hz_diff : g₂ z - f₂ z = 0 := by
        simpa [h, Set.piecewise_eq_of_notMem, hzball] using hz_zero
      exact (sub_eq_zero.mp hz_diff).symm
  exact ⟨hf₁_eq, hf₂_eq⟩
