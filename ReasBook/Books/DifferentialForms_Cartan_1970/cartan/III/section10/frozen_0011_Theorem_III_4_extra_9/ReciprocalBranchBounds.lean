import Mathlib
import DifferentialForms_Cartan_1970.I.section04.«0031_Exercise_16»
import DifferentialForms_Cartan_1970.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.II.section05.«0015_Proposition_5_1»
import DifferentialForms_Cartan_1970.II.section05.«0019_Theorem_2»
import DifferentialForms_Cartan_1970.II.section05.«0027_Remark_II_1_extra_17»
import DifferentialForms_Cartan_1970.II.section06.«0005_Corollary_1»
import DifferentialForms_Cartan_1970.II.section06.«0018_Exercise_3»
import DifferentialForms_Cartan_1970.II.section06.«0029_Exercise_14»
import DifferentialForms_Cartan_1970.III.section10.«0001_Definition_III_4_extra_1»
import DifferentialForms_Cartan_1970.III.section10.«0006_Proposition_4_1»
import DifferentialForms_Cartan_1970.III.section10.«0008_Definition_III_4_extra_6»
import DifferentialForms_Cartan_1970.III.section10.«0009_Theorem_III_4_extra_7»
import DifferentialForms_Cartan_1970.III.section10.«0010_Remark_III_4_extra_8»
import DifferentialForms_Cartan_1970.III.section10.frozen_0011_Theorem_III_4_extra_9.ImageNormalization
import DifferentialForms_Cartan_1970.III.section10.frozen_0011_Theorem_III_4_extra_9.PuncturedBallNormalForm

open Metric Set
open scoped Topology unitInterval

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if the image of a punctured
ball omits at most one value, then it is either all of `ℂ` or the complement of a singleton. -/
lemma puncturedBallImage_eq_univ_or_compl_singleton_of_compl_subsingleton
    {f : ℂ → ℂ} {o : ℂ} {ε : ℝ}
    (hcompl :
      ∀ ⦃a b : ℂ⦄,
        a ∉ f '' (ball o ε \ ({o} : Set ℂ)) →
        b ∉ f '' (ball o ε \ ({o} : Set ℂ)) →
          a = b) :
    f '' (ball o ε \ ({o} : Set ℂ)) = univ ∨
      ∃ a : ℂ, f '' (ball o ε \ ({o} : Set ℂ)) = ({a} : Set ℂ)ᶜ := by
  exact eq_univ_or_compl_singleton_of_compl_subsingleton hcompl

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: Exercise 16 gives one fixed
threshold that bounds at least one reciprocal branch at every punctured-ball point. -/
lemma pointwiseReciprocalBranchBound_onPuncturedBall
    {g : ℂ → ℂ} {ε : ℝ} :
    ∃ K : ℝ,
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ),
        ‖(g z)⁻¹‖ ≤ K ∨ ‖((1 - g z)⁻¹)‖ ≤ K := by
  rcases exists_dilog_reflection_constant_on_exercise16Domain with ⟨a, ha⟩
  let U : Set ℂ := ball (0 : ℂ) ε \ ({0} : Set ℂ)
  let E : Set ℂ := {z : ℂ | z ∈ U ∧ g z ∈ exercise16Domain}
  have hE_maps : MapsTo g E exercise16Domain := by
    -- By construction, `E` is exactly the punctured-ball preimage of `exercise16Domain`.
    intro z hz
    exact hz.2
  rcases exercise16Reflection_logProductBound (g := g) (E := E) ha hE_maps with ⟨M, hM⟩
  have hLogBound :
      ∀ z ∈ E, Real.log ‖(g z)⁻¹‖ * Real.log ‖((1 - g z)⁻¹)‖ ≤ M :=
    reciprocalLogProductBound_of_exercise16Preimage (g := g) (E := E) hE_maps hM
  have hExercise16Bound :
      ∀ z ∈ E,
        ‖(g z)⁻¹‖ ≤ Real.exp (max M 1) ∨ ‖((1 - g z)⁻¹)‖ ≤ Real.exp (max M 1) :=
    reciprocalPointwiseBound_of_exercise16LogProduct (g := g) (E := E) hE_maps hLogBound
  have hK_ge_one : (1 : ℝ) ≤ Real.exp (max M 1) := by
    -- Outside `exercise16Domain` we only get the coarse branch bound `≤ 1`, so the exponential
    -- threshold must dominate that fallback bound.
    exact Real.one_le_exp <| le_trans (by norm_num) (le_max_right M 1)
  refine ⟨Real.exp (max M 1), ?_⟩
  intro z hz
  by_cases hzE : g z ∈ exercise16Domain
  · -- On the lens preimage, the logarithmic product estimate already gives the pointwise branch.
    exact hExercise16Bound z ⟨hz, hzE⟩
  · -- Outside the lens domain, one reciprocal branch is automatically bounded by `1`.
    rcases reciprocalNorm_le_one_of_not_mem_exercise16Domain hzE with hg_inv | hone_sub_inv
    · left
      exact le_trans hg_inv hK_ge_one
    · right
      exact le_trans hone_sub_inv hK_ge_one

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: expose the Exercise-16
logarithmic threshold `T = max M 1` behind the coarse reciprocal bound `exp T`. -/
lemma exercise16ReciprocalLogThreshold_onPuncturedBall
    {g : ℂ → ℂ} {ε : ℝ}
    (h0 : 0 ∉ g '' (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (h1 : 1 ∉ g '' (ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    ∃ T : ℝ, 1 ≤ T ∧
      (∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ),
        g z ∈ exercise16Domain →
          Real.log ‖(g z)⁻¹‖ * Real.log ‖((1 - g z)⁻¹)‖ ≤ T) ∧
      (∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ),
        Real.log ‖(g z)⁻¹‖ ≤ T ∨ Real.log ‖((1 - g z)⁻¹)‖ ≤ T) := by
  rcases exists_dilog_reflection_constant_on_exercise16Domain with ⟨a, ha⟩
  let U : Set ℂ := ball (0 : ℂ) ε \ ({0} : Set ℂ)
  let E : Set ℂ := {z : ℂ | z ∈ U ∧ g z ∈ exercise16Domain}
  have hE_maps : MapsTo g E exercise16Domain := by
    -- By construction, `E` is the punctured-ball preimage of the Exercise-16 lens domain.
    intro z hz
    exact hz.2
  rcases exercise16Reflection_logProductBound (g := g) (E := E) ha hE_maps with ⟨M, hM⟩
  have hLogProduct :
      ∀ z ∈ E, Real.log ‖(g z)⁻¹‖ * Real.log ‖((1 - g z)⁻¹)‖ ≤ M :=
    reciprocalLogProductBound_of_exercise16Preimage (g := g) (E := E) hE_maps hM
  let T : ℝ := max M 1
  have hT_ge_one : 1 ≤ T := by
    -- The source threshold is normalized to dominate the fallback bound `1`.
    dsimp [T]
    exact le_max_right M 1
  have hT_nonneg : 0 ≤ T := by
    exact le_trans (by norm_num) hT_ge_one
  refine ⟨T, hT_ge_one, ?_, ?_⟩
  · intro z hz hzE
    -- On the Exercise-16 preimage we retain the sharper logarithmic product estimate.
    exact le_trans (hLogProduct z ⟨hz, hzE⟩) <| by
      dsimp [T]
      exact le_max_left M 1
  · intro z hz
    have hg_nonzero : g z ≠ 0 := by
      -- Omitting `0` keeps the reciprocal logarithm on the honest positive branch.
      intro hgz
      exact h0 ⟨z, hz, hgz⟩
    have hone_sub_nonzero : 1 - g z ≠ 0 := by
      -- Omitting `1` gives the same nonvanishing fact for `1 - g z`.
      intro h1z
      exact h1 ⟨z, hz, (sub_eq_zero.mp h1z).symm⟩
    by_cases hzE : g z ∈ exercise16Domain
    · -- On the lens preimage, convert the norm-scale owner bound back to logarithms.
      have hbound :
          ‖(g z)⁻¹‖ ≤ Real.exp T ∨ ‖((1 - g z)⁻¹)‖ ≤ Real.exp T := by
        dsimp [T]
        exact reciprocalPointwiseBound_of_exercise16LogProduct
          (g := g) (E := E) hE_maps hLogProduct z ⟨hz, hzE⟩
      rcases hbound with hg_bound | hone_sub_bound
      · left
        have hpos : 0 < ‖(g z)⁻¹‖ := by
          exact norm_pos_iff.mpr (inv_ne_zero hg_nonzero)
        exact (Real.log_le_iff_le_exp hpos).2 hg_bound
      · right
        have hpos : 0 < ‖((1 - g z)⁻¹)‖ := by
          exact norm_pos_iff.mpr (inv_ne_zero hone_sub_nonzero)
        exact (Real.log_le_iff_le_exp hpos).2 hone_sub_bound
    · -- Outside the lens domain, one reciprocal is already bounded by `1`, hence by `T`.
      rcases reciprocalNorm_le_one_of_not_mem_exercise16Domain hzE with hg_bound | hone_sub_bound
      · left
        have hlog_nonpos : Real.log ‖(g z)⁻¹‖ ≤ 0 := by
          exact Real.log_nonpos (norm_nonneg _) hg_bound
        exact le_trans hlog_nonpos hT_nonneg
      · right
        have hlog_nonpos : Real.log ‖((1 - g z)⁻¹)‖ ≤ 0 := by
          exact Real.log_nonpos (norm_nonneg _) hone_sub_bound
        exact le_trans hlog_nonpos hT_nonneg

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: on every sufficiently small
punctured ball around an essential singularity, some point on a small centered circle maps into the
Exercise 16 lens domain. -/
lemma exercise16Hit_onSmallCircle
    {g : ℂ → ℂ} {ε δ : ℝ}
    (hess : HasEssentialSingularityAt g 0) (hε : 0 < ε) (hδ : 0 < δ)
    (hg : AnalyticOnNhd ℂ g (ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    ∃ ρ, 0 < ρ ∧ ρ < min δ ε ∧ ∃ w : ℂ, ‖w‖ = ρ ∧ g w ∈ exercise16Domain := by
  obtain ⟨w, hw, hwE⟩ := exercise16Domain_preimage_accumulates_at_zero hess hε hδ hg
  refine ⟨‖w‖, ?_, ?_, w, rfl, hwE⟩
  · -- The punctured-ball witness gives a genuinely positive radius.
    exact norm_pos_iff.mpr hw.2
  · -- Its norm still lies below the same `min δ ε` radius.
    simpa [Metric.mem_ball, dist_eq_norm] using hw.1

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: every point on the radius-`ρ`
circle is hit by the standard circle parameterization. -/
lemma exists_param_standardCirclePath_eq_of_norm_eq
    {ρ : ℝ} (hρpos : 0 < ρ) {z : ℂ} (hz : ‖z‖ = ρ) :
    ∃ t : I, standardCirclePath ⟨ρ, le_of_lt hρpos⟩ t = z := by
  have hz_sphere : z ∈ Metric.sphere (0 : ℂ) ρ := by
    simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
  have hz_image : z ∈ circleMap 0 ρ '' Set.Ioc 0 (2 * Real.pi) := by
    rw [image_circleMap_Ioc, Metric.mem_sphere, dist_eq_norm, sub_zero,
      abs_of_nonneg (le_of_lt hρpos)]
    exact hz
  rcases hz_image with ⟨θ, hθ, hθz⟩
  have htwo_pi_pos : 0 < 2 * Real.pi := by positivity
  have htwo_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt htwo_pi_pos
  let t : I :=
    ⟨θ / (2 * Real.pi), by
      constructor
      · exact div_nonneg hθ.1.le htwo_pi_pos.le
      · have hdiv :
            θ / (2 * Real.pi) ≤ (2 * Real.pi) / (2 * Real.pi) := by
            exact div_le_div_of_nonneg_right hθ.2 htwo_pi_pos.le
        simpa [htwo_pi_ne] using hdiv⟩
  refine ⟨t, ?_⟩
  -- Rewrite the circle parameter by rescaling the angle from `Ioc (0, 2π]` back to `I`.
  rw [standardCirclePath_apply]
  change circleMap 0 ρ (2 * Real.pi * ((t : I) : ℝ)) = z
  have ht_eq : 2 * Real.pi * ((t : I) : ℝ) = θ := by
    dsimp [t]
    field_simp [htwo_pi_ne]
  rw [ht_eq]
  exact hθz

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if the two reciprocal branches
are both too large somewhere on the same centered circle, then the quotient selector vanishes at a
point of that same circle. -/
lemma circleSelectorZero_of_mixedLargeBranches
    {g : ℂ → ℂ} {ε ρ K : ℝ} {zNeg zPos : ℂ}
    (hρpos : 0 < ρ) (hρε : ρ < ε)
    (hzNeg_norm : ‖zNeg‖ = ρ) (hzPos_norm : ‖zPos‖ = ρ)
    (hbranch :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ),
        ‖(g z)⁻¹‖ ≤ K ∨ ‖((1 - g z)⁻¹)‖ ≤ K)
    (hg_nonzero :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hselector_cont :
      ContinuousOn (fun z ↦ Real.log ‖g z / (1 - g z)‖) (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hzNegLarge : K < ‖(g zNeg)⁻¹‖)
    (hzPosLarge : K < ‖((1 - g zPos)⁻¹)‖) :
    ∃ z₀, ‖z₀‖ = ρ ∧ Real.log ‖g z₀ / (1 - g z₀)‖ = 0 := by
  let γ : I → ℂ := fun t ↦ standardCirclePath ⟨ρ, le_of_lt hρpos⟩ t
  have hγ_mem : ∀ t : I, γ t ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    intro t
    constructor
    · -- Every point of the radius-`ρ` standard circle stays inside the ambient radius-`ε` ball.
      have hnorm : ‖γ t‖ = ρ := by
        change ‖circleMap 0 (((⟨ρ, le_of_lt hρpos⟩ : NNReal) : ℝ)) (2 * Real.pi * (t : ℝ))‖ = ρ
        rw [norm_circleMap_zero, abs_of_nonneg (le_of_lt hρpos)]
      simpa [Metric.mem_ball, dist_eq_norm, hnorm] using hρε
    · -- The same radius computation keeps the parameterized circle away from the puncture.
      have hnorm : ‖γ t‖ = ρ := by
        change ‖circleMap 0 (((⟨ρ, le_of_lt hρpos⟩ : NNReal) : ℝ)) (2 * Real.pi * (t : ℝ))‖ = ρ
        rw [norm_circleMap_zero, abs_of_nonneg (le_of_lt hρpos)]
      exact norm_ne_zero_iff.mp <| by simpa [hnorm] using hρpos.ne'
  obtain ⟨tNeg, htNeg⟩ := exists_param_standardCirclePath_eq_of_norm_eq hρpos hzNeg_norm
  obtain ⟨tPos, htPos⟩ := exists_param_standardCirclePath_eq_of_norm_eq hρpos hzPos_norm
  have hγ_tNeg : γ tNeg = zNeg := by
    simpa [γ] using htNeg
  have hγ_tPos : γ tPos = zPos := by
    simpa [γ] using htPos
  let selector : I → ℝ := fun t ↦ Real.log (‖g (γ t)‖ / ‖1 - g (γ t)‖)
  have hselector_circle_cont : Continuous selector := by
    -- Restrict the punctured-ball selector continuity along the standard-circle parameterization.
    have hcontOnRaw :
        ContinuousOn
          (fun t : I ↦ Real.log ‖g (γ t) / (1 - g (γ t))‖)
          (Set.univ : Set I) := by
      exact hselector_cont.comp
        ((standardCirclePath ⟨ρ, le_of_lt hρpos⟩).continuous.continuousOn)
        (by
          intro t ht
          exact hγ_mem t)
    have hcontRaw :
        Continuous (fun t : I ↦ Real.log ‖g (γ t) / (1 - g (γ t))‖) := by
      simpa [continuousOn_univ] using hcontOnRaw
    simpa [selector, norm_div] using hcontRaw
  have hselector_neg : selector tNeg < 0 := by
    -- The failed `g⁻¹` bound forces a strict negative selector value at `zNeg`.
    simpa [selector, norm_div] using selectorNegOfLargeReciprocal
      (hg_nonzero (γ tNeg) (hγ_mem tNeg))
      (hone_sub_nonzero (γ tNeg) (hγ_mem tNeg))
      (hbranch (γ tNeg) (hγ_mem tNeg))
      (by simpa [hγ_tNeg] using hzNegLarge)
  have hselector_pos : 0 < selector tPos := by
    -- The failed `(1 - g)⁻¹` bound forces the opposite strict sign at `zPos`.
    simpa [selector, norm_div] using selectorPosOfLargeOneSubReciprocal
      (hg_nonzero (γ tPos) (hγ_mem tPos))
      (hone_sub_nonzero (γ tPos) (hγ_mem tPos))
      (hbranch (γ tPos) (hγ_mem tPos))
      (by simpa [hγ_tPos] using hzPosLarge)
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (selector tNeg) (selector tPos) := by
    exact ⟨le_of_lt hselector_neg, le_of_lt hselector_pos⟩
  have hzero_range : (0 : ℝ) ∈ Set.range selector := by
    exact intermediate_value_univ tNeg tPos hselector_circle_cont hzero_mem
  rcases hzero_range with ⟨t₀, ht₀⟩
  refine ⟨γ t₀, ?_, ?_⟩
  · -- The standard-circle parameterization stays on the radius-`ρ` circle.
    change ‖circleMap 0 (((⟨ρ, le_of_lt hρpos⟩ : NNReal) : ℝ)) (2 * Real.pi * (t₀ : ℝ))‖ = ρ
    rw [norm_circleMap_zero, abs_of_nonneg (le_of_lt hρpos)]
  · simpa [selector, norm_div] using ht₀

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the same-circle zero-selector
bridge is easier to use on the logarithmic scale coming from the Exercise-16 threshold. -/
lemma circleZeroSelector_of_mixedLargeReciprocalLogs
    {g : ℂ → ℂ} {ε ρ T : ℝ} {zNeg zPos : ℂ}
    (hρpos : 0 < ρ) (hρε : ρ < ε)
    (hzNeg_norm : ‖zNeg‖ = ρ) (hzPos_norm : ‖zPos‖ = ρ)
    (hbranch :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ),
        Real.log ‖(g z)⁻¹‖ ≤ T ∨ Real.log ‖((1 - g z)⁻¹)‖ ≤ T)
    (hg_nonzero :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hselector_cont :
      ContinuousOn (fun z ↦ Real.log ‖g z / (1 - g z)‖) (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hzNegLarge : T < Real.log ‖(g zNeg)⁻¹‖)
    (hzPosLarge : T < Real.log ‖((1 - g zPos)⁻¹)‖) :
    ∃ z₀, ‖z₀‖ = ρ ∧ Real.log ‖g z₀ / (1 - g z₀)‖ = 0 := by
  have hbranchExp :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ),
        ‖(g z)⁻¹‖ ≤ Real.exp T ∨ ‖((1 - g z)⁻¹)‖ ≤ Real.exp T := by
    intro z hz
    rcases hbranch z hz with hg_log | hone_sub_log
    · left
      have hpos : 0 < ‖(g z)⁻¹‖ := by
        exact norm_pos_iff.mpr (inv_ne_zero (hg_nonzero z hz))
      exact (Real.log_le_iff_le_exp hpos).1 hg_log
    · right
      have hpos : 0 < ‖((1 - g z)⁻¹)‖ := by
        exact norm_pos_iff.mpr (inv_ne_zero (hone_sub_nonzero z hz))
      exact (Real.log_le_iff_le_exp hpos).1 hone_sub_log
  have hzNegNormLarge : Real.exp T < ‖(g zNeg)⁻¹‖ := by
    have hzNeg_mem : zNeg ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
      constructor
      · simpa [Metric.mem_ball, dist_eq_norm, hzNeg_norm] using hρε
      · exact norm_ne_zero_iff.mp <| by simpa [hzNeg_norm] using hρpos.ne'
    have hpos : 0 < ‖(g zNeg)⁻¹‖ := by
      exact norm_pos_iff.mpr (inv_ne_zero (hg_nonzero zNeg hzNeg_mem))
    exact (Real.lt_log_iff_exp_lt hpos).1 hzNegLarge
  have hzPosNormLarge : Real.exp T < ‖((1 - g zPos)⁻¹)‖ := by
    have hzPos_mem : zPos ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
      constructor
      · simpa [Metric.mem_ball, dist_eq_norm, hzPos_norm] using hρε
      · exact norm_ne_zero_iff.mp <| by simpa [hzPos_norm] using hρpos.ne'
    have hpos : 0 < ‖((1 - g zPos)⁻¹)‖ := by
      exact norm_pos_iff.mpr (inv_ne_zero (hone_sub_nonzero zPos hzPos_mem))
    exact (Real.lt_log_iff_exp_lt hpos).1 hzPosLarge
  -- Keep the raw-circle transport confined to the existing norm-scale circle bridge.
  exact circleSelectorZero_of_mixedLargeBranches
    (hρpos := hρpos)
    (hρε := hρε)
    (hzNeg_norm := hzNeg_norm)
    (hzPos_norm := hzPos_norm)
    (hbranch := hbranchExp)
    (hg_nonzero := hg_nonzero)
    (hone_sub_nonzero := hone_sub_nonzero)
    (hselector_cont := hselector_cont)
    (hzNegLarge := hzNegNormLarge)
    (hzPosLarge := hzPosNormLarge)

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: a vanishing quotient selector
forces the two reciprocal logarithms to coincide. -/
lemma reciprocalLogs_eq_of_logQuotientEqZero
    {g : ℂ → ℂ} {z : ℂ}
    (hg_nonzero : g z ≠ 0)
    (hone_sub_nonzero : 1 - g z ≠ 0)
    (hselector : Real.log ‖g z / (1 - g z)‖ = 0) :
    Real.log ‖((1 - g z)⁻¹)‖ = Real.log ‖(g z)⁻¹‖ := by
  -- Rewrite the selector as the difference of the two reciprocal logarithms.
  have hlogDiff :
      Real.log ‖g z / (1 - g z)‖ =
        Real.log ‖((1 - g z)⁻¹)‖ - Real.log ‖(g z)⁻¹‖ := by
    simpa [sub_eq_add_neg] using
      log_norm_div_eq_reciprocalLogDiff hg_nonzero hone_sub_nonzero
  rw [hlogDiff] at hselector
  linarith

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if the quotient selector
vanishes at a punctured-ball point, then the global Exercise-16 threshold already bounds both
reciprocal logarithms there. -/
lemma reciprocalLogs_le_of_logQuotientEqZero
    {g : ℂ → ℂ} {ε T : ℝ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hg_nonzero :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hbranch :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ),
        Real.log ‖(g z)⁻¹‖ ≤ T ∨ Real.log ‖((1 - g z)⁻¹)‖ ≤ T)
    (hselector : Real.log ‖g z / (1 - g z)‖ = 0) :
    Real.log ‖(g z)⁻¹‖ ≤ T ∧ Real.log ‖((1 - g z)⁻¹)‖ ≤ T := by
  -- First identify the two reciprocal logarithms at the zero-selector point.
  have hlogEq :
      Real.log ‖((1 - g z)⁻¹)‖ = Real.log ‖(g z)⁻¹‖ :=
    reciprocalLogs_eq_of_logQuotientEqZero
      (hg_nonzero z hz) (hone_sub_nonzero z hz) hselector
  -- Then transport the one-sided global threshold bound to the other branch.
  rcases hbranch z hz with hgz_le | hone_sub_le
  · refine ⟨hgz_le, ?_⟩
    rw [hlogEq]
    exact hgz_le
  · refine ⟨?_, hone_sub_le⟩
    rw [← hlogEq]
    exact hone_sub_le

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: once the quotient selector has
one sign on a centered circle, the pointwise reciprocal-branch bound collapses to one uniform
branch bound on that circle. -/
lemma uniformReciprocalBranch_onCircle
    {g : ℂ → ℂ} {ε ρ K : ℝ}
    (hρpos : 0 < ρ) (hρε : ρ < ε)
    (hbranch :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ),
        ‖(g z)⁻¹‖ ≤ K ∨ ‖((1 - g z)⁻¹)‖ ≤ K)
    (hg_nonzero :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hselector_sign :
      (∀ z, ‖z‖ = ρ → 0 ≤ Real.log ‖g z / (1 - g z)‖) ∨
        (∀ z, ‖z‖ = ρ → Real.log ‖g z / (1 - g z)‖ ≤ 0)) :
    (∀ z, ‖z‖ = ρ → ‖(g z)⁻¹‖ ≤ K) ∨
      (∀ z, ‖z‖ = ρ → ‖((1 - g z)⁻¹)‖ ≤ K) := by
  rcases hselector_sign with hselector_nonneg | hselector_nonpos
  · refine Or.inl ?_
    intro z hz
    have hz_mem : z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
      constructor
      · -- A point on the radius-`ρ` circle still lies inside the ambient punctured ball.
        simpa [Metric.mem_ball, dist_eq_norm, hz] using hρε
      · exact norm_ne_zero_iff.mp <| by simpa [hz] using hρpos.ne'
    -- A nonnegative selector forces the `g⁻¹` branch at the same circle point.
    exact reciprocalBound_of_logQuotientNonneg
      (hg_nonzero z hz_mem) (hone_sub_nonzero z hz_mem) (hbranch z hz_mem)
      (hselector_nonneg z hz)
  · refine Or.inr ?_
    intro z hz
    have hz_mem : z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
      constructor
      · -- The same circle-membership computation feeds the opposite selector-sign case.
        simpa [Metric.mem_ball, dist_eq_norm, hz] using hρε
      · exact norm_ne_zero_iff.mp <| by simpa [hz] using hρpos.ne'
    -- A nonpositive selector forces the `(1 - g)⁻¹` branch at the same circle point.
    exact reciprocalBound_of_logQuotientNonpos
      (hg_nonzero z hz_mem) (hone_sub_nonzero z hz_mem) (hbranch z hz_mem)
      (hselector_nonpos z hz)

