import DifferentialForms_Cartan_1970.III.section10.frozen_0011_Theorem_III_4_extra_9.NormalizedRatioMeromorphic
import DifferentialForms_Cartan_1970.III.section10.frozen_0011_Theorem_III_4_extra_9.ReciprocalBranchBounds
import DifferentialForms_Cartan_1970.III.section10.frozen_0011_Theorem_III_4_extra_9.SelectorGeometry

open Metric Set
open scoped Topology unitInterval

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if the witness-circle selector
vanishes at angle `θ`, then the global Exercise-16 threshold already bounds both reciprocal
logarithms at the corresponding circle point. -/
lemma reciprocalLogs_le_of_circleSelectorEqZero
    {g : ℂ → ℂ} {ε ρ T : ℝ} {θ : ℝ}
    (hz : circleMap 0 ρ θ ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hg_nonzero :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hbranch :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ),
        Real.log ‖(g z)⁻¹‖ ≤ T ∨ Real.log ‖((1 - g z)⁻¹)‖ ≤ T)
    (hselector : Real.log ‖g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ))‖ = 0) :
    Real.log ‖(g (circleMap 0 ρ θ))⁻¹‖ ≤ T ∧
      Real.log ‖((1 - g (circleMap 0 ρ θ))⁻¹)‖ ≤ T := by
  simpa using
    reciprocalLogs_le_of_logQuotientEqZero
      (z := circleMap 0 ρ θ)
      (ε := ε)
      (T := T)
      hz
      hg_nonzero
      hone_sub_nonzero
      hbranch
      hselector

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: mixed large reciprocal
logarithms on one centered circle already produce a zero-selector point on that same circle where
both reciprocal logarithms are bounded by the global threshold. -/
lemma mixedLargeReciprocalLogs_giveZeroSelectorWithBoundedLogs
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
    ∃ z₀, ‖z₀‖ = ρ ∧
      Real.log ‖g z₀ / (1 - g z₀)‖ = 0 ∧
      Real.log ‖(g z₀)⁻¹‖ ≤ T ∧
      Real.log ‖((1 - g z₀)⁻¹)‖ ≤ T := by
  obtain ⟨z₀, hz₀_norm, hz₀_selector⟩ :=
    circleZeroSelector_of_mixedLargeReciprocalLogs
      (g := g) (ε := ε) (ρ := ρ) (T := T)
      hρpos hρε hzNeg_norm hzPos_norm hbranch hg_nonzero hone_sub_nonzero
      hselector_cont hzNegLarge hzPosLarge
  have hz₀_mem : z₀ ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    constructor
    · simpa [Metric.mem_ball, dist_eq_norm, hz₀_norm] using hρε
    · exact norm_ne_zero_iff.mp <| by simpa [hz₀_norm] using hρpos.ne'
  have hz₀_logs :
      Real.log ‖(g z₀)⁻¹‖ ≤ T ∧
        Real.log ‖((1 - g z₀)⁻¹)‖ ≤ T :=
    reciprocalLogs_le_of_logQuotientEqZero
      (z := z₀) (ε := ε) (T := T)
      hz₀_mem
      hg_nonzero
      hone_sub_nonzero
      hbranch
      hz₀_selector
  exact ⟨z₀, hz₀_norm, hz₀_selector, hz₀_logs.1, hz₀_logs.2⟩

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: an explicit punctured-ball
normal form `c * z^n * exp (F z)` makes the normalized ratio analytic on that punctured ball. -/
lemma analyticOnNhd_ratio_of_puncturedBallNormalForm
    {g F : ℂ → ℂ} {ε : ℝ} {n : ℤ} {c : ℂ}
    (hF_analytic : AnalyticOnNhd ℂ F (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hEqRatio :
      EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    AnalyticOnNhd ℂ (fun z ↦ g z / (1 - g z)) (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
  let U : Set ℂ := ball (0 : ℂ) ε \ ({0} : Set ℂ)
  have hU_open : IsOpen U := by
    simpa [U, Set.diff_eq] using Metric.isOpen_ball.inter isOpen_ne
  have hmodel_diff :
      DifferentiableOn ℂ (fun z ↦ c * z ^ n * Complex.exp (F z)) U := by
    intro z hz
    have hzpow_diff : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ n) z :=
      (differentiableAt_id : DifferentiableAt ℂ (fun w : ℂ ↦ w) z).zpow (Or.inl hz.2)
    have hFz : AnalyticAt ℂ F z := by
      exact hF_analytic z (by simpa [U] using hz)
    exact
      ((hzpow_diff.const_mul c).mul
        (Complex.differentiableAt_exp.comp z hFz.differentiableAt)).differentiableWithinAt
  have hmodel_analytic :
      AnalyticOnNhd ℂ (fun z ↦ c * z ^ n * Complex.exp (F z)) U :=
    hmodel_diff.analyticOnNhd hU_open
  simpa [U] using
    AnalyticOnNhd.congr hU_open hmodel_analytic
      (fun z hz ↦ (hEqRatio (by simpa [U] using hz)).symm)

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if the normalized ratio
`ratio = g / (1 - g)` is analytic on an open punctured set and omits `-1`, then the omitted-value
algebraic reconstruction `g = ratio / (ratio + 1)` is analytic on the same set. -/
lemma analyticOnNhd_of_ratio_eq_div
    {g ratio : ℂ → ℂ} {U : Set ℂ}
    (hU_open : IsOpen U)
    (hratio_analytic : AnalyticOnNhd ℂ ratio U)
    (hratio_omits_negOne : (-1 : ℂ) ∉ ratio '' U)
    (hratio_eq : EqOn ratio (fun z ↦ g z / (1 - g z)) U)
    (hone_sub_nonzero : ∀ z ∈ U, 1 - g z ≠ 0) :
    AnalyticOnNhd ℂ g U := by
  have hratio_plus_one_analytic :
      AnalyticOnNhd ℂ (fun z ↦ ratio z + 1) U := by
    simpa using hratio_analytic.add analyticOnNhd_const
  have hratio_plus_one_nonzero : ∀ z ∈ U, ratio z + 1 ≠ 0 := by
    intro z hz hz1
    have hz_ratio : ratio z = (-1 : ℂ) := eq_neg_iff_add_eq_zero.mpr hz1
    exact hratio_omits_negOne ⟨z, hz, hz_ratio⟩
  have hreconstructed :
      AnalyticOnNhd ℂ (fun z ↦ ratio z / (ratio z + 1)) U := by
    simpa using hratio_analytic.div hratio_plus_one_analytic hratio_plus_one_nonzero
  refine AnalyticOnNhd.congr hU_open hreconstructed ?_
  intro z hz
  have hz1 : 1 - g z ≠ 0 := hone_sub_nonzero z hz
  have hratio_eq_z : ratio z = g z / (1 - g z) := hratio_eq hz
  have hratio_add_one : ratio z + 1 = (1 : ℂ) / (1 - g z) := by
    rw [hratio_eq_z]
    field_simp [hz1]
    ring
  calc
    ratio z / (ratio z + 1) = (g z / (1 - g z)) / (ratio z + 1) := by
      rw [hratio_eq_z]
    _ = (g z / (1 - g z)) / ((1 : ℂ) / (1 - g z)) := by
      rw [hratio_add_one]
    _ = g z / (1 - g z) * (1 - g z) := by
      field_simp [hz1]
    _ = g z := by
      field_simp [hz1]

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: a vanishing reciprocal
logarithm forces the original norm to equal `1`. -/
lemma norm_eq_one_of_log_norm_inv_eq_zero {z : ℂ} (hz : z ≠ 0)
    (hlog : Real.log ‖z⁻¹‖ = 0) :
    ‖z‖ = 1 := by
  have hnorm_inv_pos : 0 < ‖z⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hz)
  have hnorm_inv_eq : ‖z⁻¹‖ = 1 := by
    rcases (Real.log_eq_zero).1 hlog with hzero | hone | hneg
    · exact (hnorm_inv_pos.ne' hzero).elim
    · exact hone
    · exfalso
      linarith
  have hnorm_ne : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnorm_eq_inv := congrArg (fun x : ℝ ↦ x⁻¹) hnorm_inv_eq
  simpa [norm_inv, hnorm_ne] using hnorm_eq_inv

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: on a closed legal interval of
circle parameters, the principal logarithm of the normalized ratio differs from the punctured-ball
normal form by a single integral multiple of `2π i`. -/
lemma principalLogPeriod_onClosedLegalInterval
    {g F : ℂ → ℂ} {ε ρ : ℝ} {n : ℤ} {c : ℂ} {u v : ℝ}
    (hρpos : 0 < ρ)
    (hc_ne : c ≠ 0)
    (hgzeta_cont : Continuous fun θ ↦ g (circleMap 0 ρ θ))
    (hzeta_mem : ∀ θ, circleMap 0 ρ θ ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hg_nonzero : ∀ θ, g (circleMap 0 ρ θ) ≠ 0)
    (hone_sub_nonzero : ∀ θ, 1 - g (circleMap 0 ρ θ) ≠ 0)
    (hF_analytic : AnalyticOnNhd ℂ F (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hEqRatio :
      EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (huv : u ≤ v)
    (hmaps : MapsTo (fun θ ↦ g (circleMap 0 ρ θ)) (Set.Icc u v) exercise16Domain) :
    ∃ k : ℤ,
      Set.EqOn
        (fun θ ↦ Complex.log (g (circleMap 0 ρ θ)) - Complex.log (1 - g (circleMap 0 ρ θ)))
        (fun θ ↦
          Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
            F (circleMap 0 ρ θ) + k * (2 * (Real.pi : ℂ) * Complex.I))
        (Set.Icc u v) := by
  let logRatio : ℝ → ℂ := fun θ ↦
    Complex.log (g (circleMap 0 ρ θ)) - Complex.log (1 - g (circleMap 0 ρ θ))
  let normalForm : ℝ → ℂ := fun θ ↦
    Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) + F (circleMap 0 ρ θ)
  have hlogRatio_cont : ContinuousOn logRatio (Set.Icc u v) := by
    have hlogg_cont :
        ContinuousOn (fun θ ↦ Complex.log (g (circleMap 0 ρ θ))) (Set.Icc u v) := by
      exact hgzeta_cont.continuousOn.clog <| by
        intro θ hθ
        exact (exercise16Domain_mem_slitPlane (hmaps hθ)).1
    have honeSub_maps :
        MapsTo (fun θ ↦ 1 - g (circleMap 0 ρ θ)) (Set.Icc u v) exercise16Domain := by
      intro θ hθ
      exact exercise16Domain_one_sub_mem (hmaps hθ)
    have honeSub_cont :
        ContinuousOn (fun θ ↦ 1 - g (circleMap 0 ρ θ)) (Set.Icc u v) := by
      exact continuousOn_const.sub hgzeta_cont.continuousOn
    have hlogOneSub_cont :
        ContinuousOn (fun θ ↦ Complex.log (1 - g (circleMap 0 ρ θ))) (Set.Icc u v) := by
      exact honeSub_cont.clog <| by
        intro θ hθ
        exact (exercise16Domain_mem_slitPlane (honeSub_maps hθ)).1
    exact hlogg_cont.sub hlogOneSub_cont
  have hnormalForm_cont : ContinuousOn normalForm (Set.Icc u v) := by
    have hF_cont : ContinuousOn F (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := hF_analytic.continuousOn
    have hFzeta_cont : ContinuousOn (fun θ ↦ F (circleMap 0 ρ θ)) (Set.Icc u v) := by
      exact hF_cont.comp (continuous_circleMap 0 ρ).continuousOn <| by
        intro θ hθ
        exact hzeta_mem θ
    have hlinear_cont :
        ContinuousOn (fun θ : ℝ ↦ (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I))
          (Set.Icc u v) := by
      fun_prop
    simpa [normalForm, add_assoc] using continuousOn_const.add (hlinear_cont.add hFzeta_cont)
  have hexp_eq :
      Set.EqOn (fun θ ↦ Complex.exp (logRatio θ)) (fun θ ↦ Complex.exp (normalForm θ))
        (Set.Icc u v) := by
    intro θ hθ
    have hzetaθ_mem : circleMap 0 ρ θ ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ) := hzeta_mem θ
    have hgzeta_ne : g (circleMap 0 ρ θ) ≠ 0 := hg_nonzero θ
    have honeSub_ne : 1 - g (circleMap 0 ρ θ) ≠ 0 := hone_sub_nonzero θ
    have hρ_ne : (ρ : ℂ) ≠ 0 := by
      exact_mod_cast hρpos.ne'
    have hbase_exp :
        Complex.exp (Complex.log (ρ : ℂ) + θ * Complex.I) = circleMap 0 ρ θ := by
      simp [circleMap, Complex.exp_add, Complex.exp_log, hρ_ne, mul_comm, mul_left_comm, mul_assoc]
    calc
      Complex.exp (logRatio θ) = g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ)) := by
        change Complex.exp (Complex.log (g (circleMap 0 ρ θ)) -
            Complex.log (1 - g (circleMap 0 ρ θ))) =
          g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ))
        rw [Complex.exp_sub, Complex.exp_log hgzeta_ne, Complex.exp_log honeSub_ne]
      _ = c * circleMap 0 ρ θ ^ n * Complex.exp (F (circleMap 0 ρ θ)) := hEqRatio hzetaθ_mem
      _ = Complex.exp (Complex.log c) *
            Complex.exp ((n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I)) *
              Complex.exp (F (circleMap 0 ρ θ)) := by
            rw [Complex.exp_log hc_ne, Complex.exp_int_mul, hbase_exp]
      _ = Complex.exp (normalForm θ) := by
            simp [normalForm, Complex.exp_add, add_assoc, add_left_comm, add_comm, mul_assoc]
  rcases eqOn_add_two_pi_I_mul_int_of_exp_eq_on_preconnected_real
      (hE := isPreconnected_Icc) hlogRatio_cont hnormalForm_cont hexp_eq with ⟨k, hk⟩
  refine ⟨-k, ?_⟩
  intro θ hθ
  have hkθ := hk hθ
  calc
    logRatio θ = normalForm θ - k * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hkθ]
      ring
    _ = normalForm θ + (((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
      rw [sub_eq_add_neg]
      simp [neg_mul]
    _ =
        (fun θ ↦
          Complex.log c + (n : ℂ) * (Complex.log (ρ : ℂ) + θ * Complex.I) +
            F (circleMap 0 ρ θ) + (((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) θ := by
      simp [normalForm, add_assoc]

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the mixed-large-circle
obstruction belongs to the normal-form transport layer, because the contradiction has to combine
the selector-zero point on the radius-`ρ'` circle with the witness-circle principal-log packet on
`Set.Icc u v`. -/
lemma zeroSelectorNormalFormOfNormEq
    {g F : ℂ → ℂ} {ε ρ' : ℝ} {n : ℤ} {c z₀ : ℂ}
    (hρ'pos : 0 < ρ')
    (hEqRatio :
      EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hc_ne : c ≠ 0)
    (hz₀_mem : z₀ ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hz₀_norm : ‖z₀‖ = ρ')
    (hz₀_selector : Real.log ‖g z₀ / (1 - g z₀)‖ = 0) :
    ∃ θ : ℝ,
      circleMap 0 ρ' θ = z₀ ∧
        Real.log ‖c‖ + (n : ℝ) * Real.log ρ' + (F z₀).re = 0 := by
  obtain ⟨t, ht⟩ := exists_param_standardCirclePath_eq_of_norm_eq hρ'pos hz₀_norm
  let θ : ℝ := 2 * Real.pi * (t : ℝ)
  have hcircle : circleMap 0 ρ' θ = z₀ := by
    -- Rewrite the standard circle parameter back to the `circleMap` spelling used by the owner
    -- transport API.
    simpa [θ, standardCirclePath_apply] using ht
  refine ⟨θ, hcircle, ?_⟩
  have hzeta_mem : circleMap 0 ρ' θ ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    simpa [hcircle] using hz₀_mem
  have hnormalForm :
      Real.log ‖g (circleMap 0 ρ' θ) / (1 - g (circleMap 0 ρ' θ))‖ =
        Real.log ‖c‖ + (n : ℝ) * Real.log ρ' + (F (circleMap 0 ρ' θ)).re :=
    circleSelector_eq_normalForm
      (g := g) (F := F) (ε := ε) (ρ := ρ') (n := n) (c := c) (θ := θ)
      hρ'pos
      hc_ne
      hEqRatio
      hzeta_mem
  -- Replace the point on the `ρ'`-circle by the original witness `z₀`.
  calc
    Real.log ‖c‖ + (n : ℝ) * Real.log ρ' + (F z₀).re
        = Real.log ‖c‖ + (n : ℝ) * Real.log ρ' + (F (circleMap 0 ρ' θ)).re := by
            rw [hcircle]
    _ = Real.log ‖g (circleMap 0 ρ' θ) / (1 - g (circleMap 0 ρ' θ))‖ := by
          symm
          exact hnormalForm
    _ = 0 := by
          simpa [hcircle] using hz₀_selector

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: on a fixed witness circle, a
selector zero rewrites immediately to the real-part vanishing of the punctured-ball normal form. -/
lemma circleNormalFormRealPart_eq_zero_of_selectorEqZero
    {g F : ℂ → ℂ} {ε ρ : ℝ} {n : ℤ} {c : ℂ} {θ : ℝ}
    (hρpos : 0 < ρ) (hc_ne : c ≠ 0)
    (hEqRatio :
      EqOn (fun z ↦ g z / (1 - g z))
        (fun z ↦ c * z ^ n * Complex.exp (F z))
        (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hzeta_mem : circleMap 0 ρ θ ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hselector_zero :
      Real.log ‖g (circleMap 0 ρ θ) / (1 - g (circleMap 0 ρ θ))‖ = 0) :
    Real.log ‖c‖ + (n : ℝ) * Real.log ρ + (F (circleMap 0 ρ θ)).re = 0 := by
  -- First rewrite the selector by the normal form, then use the zero hypothesis.
  have hnormal :=
    circleSelector_eq_normalForm
      (g := g) (F := F) (ε := ε) (ρ := ρ) (n := n) (c := c) (θ := θ)
      hρpos
      hc_ne
      hEqRatio
      hzeta_mem
  linarith

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: meromorphicity of `g` on the
punctured-ball side transports to meromorphicity of the normalized ratio `g / (1 - g)`. -/
lemma ratioMeromorphic_of_gMeromorphic
    {g : ℂ → ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (hone_sub_nonzero :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hratio_omits_negOne :
      (-1 : ℂ) ∉ (fun z ↦ g z / (1 - g z)) '' (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hg_meromorphic : MeromorphicAt g 0) :
    MeromorphicAt (fun z ↦ g z / (1 - g z)) 0 := by
  let ratio : ℂ → ℂ := fun z ↦ g z / (1 - g z)
  have hnormalized_meromorphic :
      MeromorphicAt (fun z ↦ (ratio z - (0 : ℂ)) / (ratio z - (-1 : ℂ))) 0 := by
    have hEq :
        (fun z ↦ (ratio z - (0 : ℂ)) / (ratio z - (-1 : ℂ))) =ᶠ[𝓝[≠] (0 : ℂ)] g := by
      have hball :
          ball (0 : ℂ) ε \ ({0} : Set ℂ) ∈ 𝓝[≠] (0 : ℂ) := by
        rw [show ball (0 : ℂ) ε \ ({0} : Set ℂ) = ball (0 : ℂ) ε ∩ ({(0 : ℂ)}ᶜ) by
          ext z
          simp [Set.diff_eq]]
        exact Metric.mem_nhdsWithin_iff.mpr ⟨ε, hε, subset_rfl⟩
      refine Filter.mem_of_superset hball ?_
      intro z hz
      have hz_den_nonzero : 1 - g z ≠ 0 := hone_sub_nonzero z hz
      dsimp [ratio]
      field_simp [hz_den_nonzero]
      ring
    exact hg_meromorphic.congr hEq.symm
  exact meromorphicAt_of_normalizedOmittedRatio
    (f := ratio) (ε := ε) (a := 0) (b := -1) hε (by norm_num)
    hratio_omits_negOne hnormalized_meromorphic
