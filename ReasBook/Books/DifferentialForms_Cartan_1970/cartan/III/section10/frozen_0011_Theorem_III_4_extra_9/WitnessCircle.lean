import Mathlib
import DifferentialForms_Cartan_1970.cartan.I.section04.«0031_Exercise_16»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0015_Proposition_5_1»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0019_Theorem_2»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0027_Remark_II_1_extra_17»
import DifferentialForms_Cartan_1970.cartan.II.section06.«0005_Corollary_1»
import DifferentialForms_Cartan_1970.cartan.II.section06.«0018_Exercise_3»
import DifferentialForms_Cartan_1970.cartan.II.section06.«0029_Exercise_14»
import DifferentialForms_Cartan_1970.cartan.III.section10.«0001_Definition_III_4_extra_1»
import DifferentialForms_Cartan_1970.cartan.III.section10.«0006_Proposition_4_1»
import DifferentialForms_Cartan_1970.cartan.III.section10.«0008_Definition_III_4_extra_6»
import DifferentialForms_Cartan_1970.cartan.III.section10.«0009_Theorem_III_4_extra_7»
import DifferentialForms_Cartan_1970.cartan.III.section10.«0010_Remark_III_4_extra_8»
import DifferentialForms_Cartan_1970.cartan.III.section10.frozen_0011_Theorem_III_4_extra_9.LoopHomotopy
import DifferentialForms_Cartan_1970.cartan.III.section10.frozen_0011_Theorem_III_4_extra_9.PuncturedBallNormalForm

open Metric Set
open scoped Topology unitInterval

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: on a punctured ball where `g`
omits `0` and `1`, the normalized quotient `g / (1 - g)` admits the standard punctured-ball
normal form `c * z^n * exp F`. -/
lemma witnessCircleNormalizedRatioNormalForm
    {g : ℂ → ℂ} {ε ρ : ℝ}
    (hε : 0 < ε)
    (hρpos : 0 < ρ) (hρsmall : ρ < ε)
    (hg : AnalyticOnNhd ℂ g (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hg_nonzero :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0) :
    ∃ n : ℤ, ∃ F : ℂ → ℂ, ∃ c : ℂ,
      c ≠ 0 ∧
      AnalyticOnNhd ℂ F (ball (0 : ℂ) ε \ ({0} : Set ℂ)) ∧
      EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
  let U : Set ℂ := ball (0 : ℂ) ε \ ({0} : Set ℂ)
  let G : ℂ → ℂ := fun z ↦ g z / (1 - g z)
  let ρNN : NNReal := ⟨ρ, le_of_lt hρpos⟩
  let ρOuter : NNReal := ⟨(ρ + ε) / 2, by positivity⟩
  have hρ_left : (0 : NNReal) < ρNN := by
    exact_mod_cast hρpos
  have hρ_right : ρNN < ρOuter := by
    exact_mod_cast (by linarith : ρ < (ρ + ε) / 2)
  have hρOuter_lt_ε : (ρOuter : ℝ) < ε := by
    -- The auxiliary outer radius is the midpoint between `ρ` and `ε`, hence still below `ε`.
    change (ρ + ε) / 2 < ε
    nlinarith [hρsmall]
  have hG_on : AnalyticOnNhd ℂ G U := by
    -- The normalized quotient is analytic because `g` and `1 - g` are analytic and the
    -- denominator never vanishes on the punctured ball.
    simpa [G, U] using hg.div (analyticOnNhd_const.sub hg) hone_sub_nonzero
  have hG_ne : ∀ z ∈ U, G z ≠ 0 := by
    -- Omitting both values makes both numerator and denominator nonzero on the punctured ball.
    intro z hz
    exact div_ne_zero (hg_nonzero z hz) (hone_sub_nonzero z hz)
  have hU_open : IsOpen U := by
    -- The punctured ball is an honest open set.
    simpa [U, Set.diff_eq] using Metric.isOpen_ball.inter isOpen_ne
  have hG_logDeriv : AnalyticOnNhd ℂ (logDeriv G) U := by
    -- The logarithmic derivative is analytic on the same punctured ball.
    exact analyticOnNhd_logDeriv_of_avoids_zero hU_open hG_on hG_ne
  have hAnn_subset : complexOpenAnnulus (0 : NNReal) ρOuter ⊆ U := by
    -- The auxiliary annulus lies inside the punctured ball because its outer radius is still
    -- below `ε`.
    exact complexOpenAnnulus_subset_puncturedBall hρOuter_lt_ε
  have hG_diff_ann : DifferentiableOn ℂ G (complexOpenAnnulus (0 : NNReal) ρOuter) := by
    -- Restrict punctured-ball analyticity to the annulus that carries the witness circle.
    exact hG_on.differentiableOn.mono hAnn_subset
  have hG_ne_ann : ∀ z ∈ complexOpenAnnulus (0 : NNReal) ρOuter, G z ≠ 0 := by
    -- The same nonvanishing statement restricts to the annulus.
    intro z hz
    exact hG_ne z (hAnn_subset hz)
  obtain ⟨n, hn⟩ :=
    mappedStandardCirclePath_invIntegral_isInt
      (G := G) (ρ₂ := (0 : NNReal)) (ρ₁ := ρOuter) (ρ := ρNN)
      hG_diff_ann hG_ne_ann hρ_left hρ_right
  have hmappedPeriod :
      ∫ᶜ w in
        (standardCirclePath ρNN).map' <|
          (hG_diff_ann.continuousOn).mono <| by
            rintro _ ⟨t, rfl⟩
            exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t,
        indexForm 0 w =
          ((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
    -- Convert the integer-valued winding witness back to the raw contour integral.
    have hraw :
        ∫ᶜ w in
          (standardCirclePath ρNN).map' <|
            (hG_diff_ann.continuousOn).mono <| by
              rintro _ ⟨t, rfl⟩
              exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t,
          indexForm 0 w =
            (n : ℂ) * (2 * Real.pi * Complex.I : ℂ) := by
      exact (div_eq_iff Complex.two_pi_I_ne_zero).mp hn
    simpa [mul_assoc, mul_left_comm, mul_comm] using hraw
  have hperiod :
      ∫ᶜ z in standardCirclePath ρNN, ((logDeriv G) dz) z =
        ((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
    -- Replace the logarithmic-derivative integral by the mapped-loop index integral.
    calc
      ∫ᶜ z in standardCirclePath ρNN, ((logDeriv G) dz) z =
          ∫ᶜ w in
            (standardCirclePath ρNN).map' <|
              (hG_diff_ann.continuousOn).mono <| by
                rintro _ ⟨t, rfl⟩
                exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t,
            indexForm 0 w := by
              exact logDerivIntegral_eq_mappedLoopIndex_onStandardCircle
                (G := G) (ρ₂ := (0 : NNReal)) (ρ₁ := ρOuter) (ρ := ρNN)
                hG_diff_ann hG_ne_ann hρ_left hρ_right
      _ = ((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ) := hmappedPeriod
  have hloopZero :
      ∀ {z : ℂ} (γ : Path z z), γ.IsPiecewiseDifferentiable →
        Set.range γ ⊆ U →
          ∫ᶜ w in γ, ((fun z ↦ logDeriv G z - (n : ℂ) / z) dz) w = 0 := by
    -- The witness-circle period fixes the global zero-loop correction on the punctured ball.
    exact loopIntegral_logDerivSubInv_eq_zero_on_puncturedBall
      (G := G) (ε := ε) (ρ := ρNN) (n := n) hε hG_logDeriv hρpos hρsmall hperiod
  obtain ⟨F, c, hc_ne, hF_analytic, hEqG⟩ :=
    puncturedBallNormalForm_of_zeroLoopLogDerivCorrection
      (G := G) (ε := ε) (n := n) hε hG_on hG_logDeriv hG_ne hloopZero
  refine ⟨n, F, c, hc_ne, hF_analytic, ?_⟩
  -- Unpack the local abbreviations back to the normalized quotient spelling.
  simpa [G, U] using hEqG

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: points on the same positive
radius circle admit angle representatives ordered around the witness point after shifting by whole
turns. -/
lemma sameCircleAngleOrder_throughWitness
    {ρ : ℝ} {w zNeg zPos : ℂ}
    (hρpos : 0 < ρ)
    (hw_norm : ‖w‖ = ρ) (hzNeg_norm : ‖zNeg‖ = ρ) (hzPos_norm : ‖zPos‖ = ρ) :
    ∃ thetaNeg thetaW thetaPos : ℝ,
      thetaNeg < thetaW ∧ thetaW < thetaPos ∧
        circleMap 0 ρ thetaW = w ∧
        circleMap 0 ρ thetaNeg = zNeg ∧
        circleMap 0 ρ thetaPos = zPos := by
  have hw_image : w ∈ circleMap 0 ρ '' Set.Ioc 0 (2 * Real.pi) := by
    rw [image_circleMap_Ioc, Metric.mem_sphere, dist_eq_norm, sub_zero,
      abs_of_nonneg (le_of_lt hρpos)]
    exact hw_norm
  have hzNeg_image : zNeg ∈ circleMap 0 ρ '' Set.Ioc 0 (2 * Real.pi) := by
    rw [image_circleMap_Ioc, Metric.mem_sphere, dist_eq_norm, sub_zero,
      abs_of_nonneg (le_of_lt hρpos)]
    exact hzNeg_norm
  have hzPos_image : zPos ∈ circleMap 0 ρ '' Set.Ioc 0 (2 * Real.pi) := by
    rw [image_circleMap_Ioc, Metric.mem_sphere, dist_eq_norm, sub_zero,
      abs_of_nonneg (le_of_lt hρpos)]
    exact hzPos_norm
  rcases hw_image with ⟨thetaWBase, hthetaWBase, hthetaW_eq⟩
  rcases hzNeg_image with ⟨thetaNegBase, hthetaNegBase, hthetaNeg_eq⟩
  rcases hzPos_image with ⟨thetaPosBase, hthetaPosBase, hthetaPos_eq⟩
  let thetaNeg : ℝ := if thetaNegBase < thetaWBase then thetaNegBase else thetaNegBase - 2 * Real.pi
  let thetaPos : ℝ := if thetaWBase < thetaPosBase then thetaPosBase else thetaPosBase + 2 * Real.pi
  refine ⟨thetaNeg, thetaWBase, thetaPos, ?_, ?_, hthetaW_eq, ?_, ?_⟩
  · -- Shift the negative witness backward by one full turn unless it is already before `w`.
    dsimp [thetaNeg]
    by_cases hlt : thetaNegBase < thetaWBase
    · simp [hlt]
    · have hthetaNeg_le : thetaNegBase ≤ 2 * Real.pi := hthetaNegBase.2
      have hthetaNeg_nonpos : thetaNegBase - 2 * Real.pi ≤ 0 := by
        linarith
      simpa [hlt] using lt_of_le_of_lt hthetaNeg_nonpos hthetaWBase.1
  · -- Shift the positive witness forward by one full turn unless it is already after `w`.
    dsimp [thetaPos]
    by_cases hlt : thetaWBase < thetaPosBase
    · simp [hlt]
    · have hthetaW_le : thetaWBase ≤ 2 * Real.pi := hthetaWBase.2
      have hthetaPos_shift : thetaWBase < thetaPosBase + 2 * Real.pi := by
        linarith [hthetaPosBase.1, hthetaW_le]
      simpa [hlt] using hthetaPos_shift
  · -- The circle map is `2π`-periodic, so the backward shift does not change the point.
    dsimp [thetaNeg]
    by_cases hlt : thetaNegBase < thetaWBase
    · simpa [hlt] using hthetaNeg_eq
    · have hshift : circleMap 0 ρ (thetaNegBase - 2 * Real.pi) = circleMap 0 ρ thetaNegBase := by
        simpa [sub_eq_add_neg, add_assoc] using
          (periodic_circleMap (0 : ℂ) ρ (thetaNegBase - 2 * Real.pi)).symm
      simpa [hlt] using hshift.trans hthetaNeg_eq
  · -- The same `2π`-periodicity handles the forward shift for the positive witness.
    dsimp [thetaPos]
    by_cases hlt : thetaWBase < thetaPosBase
    · simpa [hlt] using hthetaPos_eq
    · have hshift : circleMap 0 ρ (thetaPosBase + 2 * Real.pi) = circleMap 0 ρ thetaPosBase := by
        simpa using periodic_circleMap (0 : ℂ) ρ thetaPosBase
      simpa [hlt] using hshift.trans hthetaPos_eq

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: continuity of `g` along the
fixed witness circle gives a smaller ordered angle interval whose image stays in
`exercise16Domain`. -/
lemma exercise16SubintervalAroundCircleWitness
    {g : ℂ → ℂ} {ε ρ thetaNeg thetaW thetaPos : ℝ}
    (hthetaNeg_lt : thetaNeg < thetaW) (hthetaW_lt : thetaW < thetaPos)
    (hwEθ : g (circleMap 0 ρ thetaW) ∈ exercise16Domain)
    (hzeta_mem :
      ∀ θ ∈ Set.Icc thetaNeg thetaPos,
        circleMap 0 ρ θ ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hg_cont : ContinuousOn g (ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    ∃ tauNeg tauPos : ℝ,
      thetaNeg < tauNeg ∧
        tauNeg < thetaW ∧
        thetaW < tauPos ∧
        tauPos < thetaPos ∧
        MapsTo (fun θ ↦ g (circleMap 0 ρ θ)) (Set.Icc tauNeg tauPos) exercise16Domain := by
  let zeta : ℝ → ℂ := fun θ ↦ circleMap 0 ρ θ
  let h : ℝ → ℂ := fun θ ↦ g (zeta θ)
  have hcont :
      ContinuousOn h (Set.Icc thetaNeg thetaPos) := by
    -- Restrict the witness-circle composition to the ordered angle interval.
    refine hg_cont.comp (continuous_circleMap 0 ρ).continuousOn ?_
    intro θ hθ
    exact hzeta_mem θ hθ
  have hthetaW_mem : thetaW ∈ Set.Icc thetaNeg thetaPos := by
    exact ⟨le_of_lt hthetaNeg_lt, le_of_lt hthetaW_lt⟩
  have hopen : IsOpen exercise16Domain := by
    -- The Exercise-16 lens domain is the intersection of two open unit balls.
    simpa [exercise16Domain] using
      (Metric.isOpen_ball.inter Metric.isOpen_ball :
        IsOpen (Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) 1))
  have hpreimage_nhds :
      h ⁻¹' exercise16Domain ∈ 𝓝[Set.Icc thetaNeg thetaPos] thetaW := by
    -- Pull the open lens neighborhood of `h thetaW` back through the circle map inside `Icc`.
    exact (hcont.continuousWithinAt hthetaW_mem) (hopen.mem_nhds hwEθ)
  rcases Metric.mem_nhdsWithin_iff.mp hpreimage_nhds with ⟨δ, hδ_pos, hδ_maps⟩
  let η : ℝ := min (δ / 2) (min ((thetaW - thetaNeg) / 2) ((thetaPos - thetaW) / 2))
  have hη_pos : 0 < η := by
    have hleft : 0 < (thetaW - thetaNeg) / 2 := by linarith
    have hright : 0 < (thetaPos - thetaW) / 2 := by linarith
    have hδ_half : 0 < δ / 2 := by positivity
    exact lt_min hδ_half (lt_min hleft hright)
  let tauNeg : ℝ := thetaW - η
  let tauPos : ℝ := thetaW + η
  refine ⟨tauNeg, tauPos, ?_, ?_, ?_, ?_, ?_⟩
  · -- Move left from `thetaW` by a strictly smaller amount than half the ordered gap.
    have hη_le : η ≤ (thetaW - thetaNeg) / 2 := by
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    dsimp [tauNeg]
    linarith
  · -- The left endpoint still lies strictly before the witness angle.
    dsimp [tauNeg]
    linarith
  · -- The right endpoint still lies strictly after the witness angle.
    dsimp [tauPos]
    linarith
  · -- Move right by less than half the remaining ordered gap.
    have hη_le : η ≤ (thetaPos - thetaW) / 2 := by
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    dsimp [tauPos]
    linarith
  · intro θ hθ
    -- Every point of the shrunken interval stays inside the pulled-back open lens neighborhood.
    have hdist_le : dist θ thetaW ≤ η := by
      rw [Real.dist_eq]
      have hsub_left : thetaW - η ≤ θ := by
        exact hθ.1
      have hsub_right : θ ≤ thetaW + η := by
        exact hθ.2
      have habs_le : |θ - thetaW| ≤ η := by
        have hneg : -η ≤ θ - thetaW := by
          linarith
        have hpos : θ - thetaW ≤ η := by
          linarith
        exact abs_le.mpr ⟨hneg, hpos⟩
      simpa [abs_sub_comm] using habs_le
    have hη_le_halfδ : η ≤ δ / 2 := min_le_left _ _
    have hθ_mem_ball : θ ∈ Metric.ball thetaW δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      have habs_le_halfδ : |θ - thetaW| ≤ δ / 2 := by
        exact le_trans (by simpa [Real.dist_eq] using hdist_le) hη_le_halfδ
      have hδ_half_lt : δ / 2 < δ := by
        linarith
      exact lt_of_le_of_lt habs_le_halfδ hδ_half_lt
    have hθ_mem_Icc : θ ∈ Set.Icc thetaNeg thetaPos := by
      have hη_le_left : η ≤ (thetaW - thetaNeg) / 2 := by
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      have hη_le_right : η ≤ (thetaPos - thetaW) / 2 := by
        exact le_trans (min_le_right _ _) (min_le_right _ _)
      constructor
      · have hthetaNeg_le_tauNeg : thetaNeg ≤ thetaW - η := by
          linarith
        exact le_trans hthetaNeg_le_tauNeg hθ.1
      · have htauPos_le_thetaPos : thetaW + η ≤ thetaPos := by
          linarith
        exact le_trans hθ.2 htauPos_le_thetaPos
    exact hδ_maps ⟨hθ_mem_ball, hθ_mem_Icc⟩

