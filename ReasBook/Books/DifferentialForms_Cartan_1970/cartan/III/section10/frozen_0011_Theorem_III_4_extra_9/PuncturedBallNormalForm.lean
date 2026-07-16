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
import DifferentialForms_Cartan_1970.cartan.III.section10.frozen_0011_Theorem_III_4_extra_9.ImageNormalization
import DifferentialForms_Cartan_1970.cartan.III.section10.frozen_0011_Theorem_III_4_extra_9.PuncturedBallConnectivity
import DifferentialForms_Cartan_1970.cartan.III.section10.frozen_0011_Theorem_III_4_extra_9.LoopHomotopy

open Metric Set
open scoped Topology unitInterval

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: once the standard-circle
period of `logDeriv G` is fixed, the correction `logDeriv G - n / z` has zero integral on every
piecewise differentiable closed loop in the punctured ball. -/
lemma loopIntegral_logDerivSubInv_eq_zero_on_puncturedBall
    {G : ℂ → ℂ} {ε : ℝ} {ρ : NNReal} {n : ℤ}
    (hε : 0 < ε)
    (hG_analytic : AnalyticOnNhd ℂ (logDeriv G) (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hρpos : 0 < (ρ : ℝ)) (hρε : (ρ : ℝ) < ε)
    (hperiod :
      ∫ᶜ z in standardCirclePath ρ, ((logDeriv G) dz) z =
        ((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ)) :
    ∀ {z : ℂ} (γ : Path z z), γ.IsPiecewiseDifferentiable →
      Set.range γ ⊆ ball (0 : ℂ) ε \ ({0} : Set ℂ) →
        ∫ᶜ w in γ, ((fun z ↦ logDeriv G z - (n : ℂ) / z) dz) w = 0 := by
  let U : Set ℂ := ball (0 : ℂ) ε \ ({0} : Set ℂ)
  have hU_open : IsOpen U := by
    -- The punctured ball is open, so the correction term is holomorphic on an honest domain.
    simpa [U, Set.diff_eq] using Metric.isOpen_ball.inter isOpen_ne
  have hInv_analytic : AnalyticOnNhd ℂ (fun z : ℂ ↦ ((n : ℂ) / z)) U := by
    -- The reciprocal is holomorphic away from `0`, and scalar multiplication preserves analyticity.
    have hzInv : AnalyticOnNhd ℂ (fun z : ℂ ↦ z⁻¹) U := by
      exact analyticOnNhd_id.inv (fun z hz ↦ hz.2)
    simpa [div_eq_mul_inv, U] using (analyticOnNhd_const.mul hzInv)
  have hCorrection_analytic :
      AnalyticOnNhd ℂ (fun z ↦ logDeriv G z - (n : ℂ) / z) U := by
    -- Package the correction term in the canonical spelling used by the later primitive theorem.
    simpa [U] using hG_analytic.sub hInv_analytic
  have hω_closed :
      IsClosedOn (Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z)) U := by
    intro z hz
    rcases holomorphic_has_local_primitive hU_open hCorrection_analytic.differentiableOn hz with
      ⟨r, hr, hball, hExact⟩
    refine ⟨Metric.ball z r, Metric.isOpen_ball, Metric.mem_ball_self hr, hball, ?_⟩
    simpa [Complex.realScalarOneForm] using hExact.hasPrimitiveOn
  intro z γ hγ_piece hγU
  obtain ⟨m, hhom⟩ :=
    closedLoop_homotopic_to_circleTurns_puncturedBall (ρ := ρ) hε hρpos hρε γ hγU
  have hcircleU : Set.range (circleTurns ρ m) ⊆ U := by
    rintro _ ⟨t, rfl⟩
    exact circleTurns_mem_puncturedBall hρpos hρε t
  have hCorrection_cont :
      ContinuousOn (Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z)) U := by
    rw [show Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z) =
        fun z ↦ (logDeriv G z - (n : ℂ) / z) • (1 : ℂ →L[ℝ] ℂ) by
          funext z
          exact Complex.realScalarOneForm_eq_smul _ z]
    exact hCorrection_analytic.continuousOn.smul
      (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ)) U)
  have hγ_integrable :
      CurveIntegrable (Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z)) γ := by
    exact Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
      (ω := Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z))
      hCorrection_cont hγ_piece hγU
  have hcircle_integrable :
      CurveIntegrable (Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z))
        (circleTurns ρ m) := by
    exact Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
      (ω := Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z))
      hCorrection_cont (circleTurns_isPiecewiseDifferentiable ρ m) hcircleU
  have hEq :
      ∫ᶜ w in γ, Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z) w =
        ∫ᶜ w in circleTurns ρ m, Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z) w :=
    Path.curveIntegral_eq_of_homotopic_closed_paths_of_closed_form
      hhom hγ_piece (circleTurns_isPiecewiseDifferentiable ρ m) hγ_integrable
      hcircle_integrable hω_closed
  have hlog_integrable :
      CurveIntegrable (Complex.realScalarOneForm (logDeriv G)) (circleTurns ρ m) := by
    rw [show Complex.realScalarOneForm (logDeriv G) =
        fun z ↦ logDeriv G z • (1 : ℂ →L[ℝ] ℂ) by
        ext z v
        simp [Complex.realScalarOneForm]]
    exact Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
      (hG_analytic.continuousOn.smul
        (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ)) U))
      (circleTurns_isPiecewiseDifferentiable ρ m) hcircleU
  have hInv_integrable :
      CurveIntegrable (Complex.realScalarOneForm (fun z : ℂ ↦ (n : ℂ) / z)) (circleTurns ρ m) := by
    rw [show Complex.realScalarOneForm (fun z : ℂ ↦ (n : ℂ) / z) =
        fun z ↦ ((n : ℂ) / z) • (1 : ℂ →L[ℝ] ℂ) by
        ext z v
        simp [Complex.realScalarOneForm]]
    exact Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
      (hInv_analytic.continuousOn.smul
        (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ)) U))
      (circleTurns_isPiecewiseDifferentiable ρ m) hcircleU
  have hcircle_log :
      ∫ᶜ w in circleTurns ρ m, ((logDeriv G) dz) w =
        (m : ℂ) * (((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ)) := by
    -- The frozen one-turn period package already controls every signed same-radius reference loop.
    exact circleTurns_logDerivIntegral_eq_int_mul_standardCirclePeriod
      (G := G) (ε := ε) (ρ := ρ)
      (c := ((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ))
      hε hG_analytic hρpos hρε hperiod m
  have hcircle_log_scalar :
      ∫ᶜ w in circleTurns ρ m, Complex.realScalarOneForm (logDeriv G) w =
        (m : ℂ) * (((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ)) := by
    rw [show Complex.realScalarOneForm (logDeriv G) =
        fun z ↦ (((logDeriv G dz) z).restrictScalars ℝ) by
        ext z v
        simp [Complex.realScalarOneForm]]
    rw [curveIntegral_restrictScalars]
    exact hcircle_log
  have hcircle_index :
      ∫ᶜ w in circleTurns ρ m, indexForm 0 w =
        (m : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) := by
    have hindex :
        (∫ᶜ w in circleTurns ρ m, indexForm 0 w) / (2 * Real.pi * Complex.I : ℂ) = (m : ℂ) := by
      have hInt : CurveIntegrable (indexForm 0) (circleTurns ρ m) :=
        circleTurns_indexForm_curveIntegrable hρpos hρε
      simpa [closedPathIndex_def, Path.closedPathIndexAt_def] using
        (circleTurns_hasIndexAt_zero ρ m hρpos).closedPathIndex_eq (circleTurns_isPiecewiseDifferentiable ρ m) hInt
    exact (div_eq_iff Complex.two_pi_I_ne_zero).mp <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hindex
  have hcircle_inv_scalar :
      ∫ᶜ w in circleTurns ρ m, Complex.realScalarOneForm (fun z : ℂ ↦ (n : ℂ) / z) w =
        (m : ℂ) * (((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ)) := by
    rw [show Complex.realScalarOneForm (fun z : ℂ ↦ (n : ℂ) / z) =
        fun z ↦ ((n : ℂ) • indexForm 0 z).restrictScalars ℝ by
        ext z v
        simp [Complex.realScalarOneForm, indexForm, div_eq_mul_inv, mul_comm, mul_left_comm]]
    rw [curveIntegral_restrictScalars]
    change curveIntegral ((n : ℂ) • indexForm 0) (circleTurns ρ m) =
      (m : ℂ) * (((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ))
    rw [curveIntegral_smul]
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun z : ℂ ↦ (n : ℂ) * z) hcircle_index
  have hcircle_correction_scalar :
      ∫ᶜ w in circleTurns ρ m, Complex.realScalarOneForm
        (fun z ↦ logDeriv G z - (n : ℂ) / z) w = 0 := by
    -- On the reference loop, the `logDeriv` period and the explicit `dz / z` period match exactly.
    rw [show Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z) =
        Complex.realScalarOneForm (logDeriv G) - Complex.realScalarOneForm (fun z : ℂ ↦ (n : ℂ) / z) by
        ext z v
        simp [Complex.realScalarOneForm, sub_mul]]
    rw [curveIntegral_sub hlog_integrable hInv_integrable, hcircle_log_scalar, hcircle_inv_scalar]
    ring
  have hfinal :
      ∫ᶜ w in γ, Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z) w = 0 :=
    hEq.trans hcircle_correction_scalar
  rw [show Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z) =
      fun z ↦ (((fun z ↦ logDeriv G z - (n : ℂ) / z) dz) z).restrictScalars ℝ by
      ext z v
      simp [Complex.realScalarOneForm]] at hfinal
  rw [curveIntegral_restrictScalars] at hfinal
  exact hfinal

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: zero loop integrals for
`logDeriv G - n / z` already produce the exact primitive used later in the punctured-ball
normal form. -/
lemma zeroLoopLogDerivPrimitive_onPuncturedBall
    {G : ℂ → ℂ} {ε : ℝ} {n : ℤ}
    (hε : 0 < ε)
    (hG_analytic : AnalyticOnNhd ℂ (logDeriv G) (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hloopZero :
      ∀ {z : ℂ} (γ : Path z z), γ.IsPiecewiseDifferentiable →
        Set.range γ ⊆ ball (0 : ℂ) ε \ ({0} : Set ℂ) →
          ∫ᶜ w in γ, ((fun z ↦ logDeriv G z - (n : ℂ) / z) dz) w = 0) :
    ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F (ball (0 : ℂ) ε \ ({0} : Set ℂ)) ∧
        ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ),
          HasDerivAt F (logDeriv G z - (n : ℂ) / z) z := by
  let U : Set ℂ := ball (0 : ℂ) ε \ ({0} : Set ℂ)
  have hU_open : IsOpen U := by
    -- The punctured ball is the open connected source set for the primitive theorem.
    simpa [U, Set.diff_eq] using Metric.isOpen_ball.inter isOpen_ne
  have hU_connected : IsConnected U :=
    (isPathConnected_puncturedBallComplex hε).isConnected
  have hCorrection_analytic :
      AnalyticOnNhd ℂ (fun z ↦ logDeriv G z - (n : ℂ) / z) U := by
    -- The only extra analytic ingredient beyond `logDeriv G` is the reciprocal on `U`.
    have hInv_analytic : AnalyticOnNhd ℂ (fun z : ℂ ↦ (n : ℂ) / z) U := by
      have hzInv : AnalyticOnNhd ℂ (fun z : ℂ ↦ z⁻¹) U := by
        exact analyticOnNhd_id.inv (fun z hz ↦ hz.2)
      simpa [div_eq_mul_inv, U] using (analyticOnNhd_const.mul hzInv)
    simpa [U] using hG_analytic.sub hInv_analytic
  have hCorrection_cont :
      ContinuousOn (Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z)) U := by
    rw [show Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z) =
        fun z ↦ (logDeriv G z - (n : ℂ) / z) • (1 : ℂ →L[ℝ] ℂ) by
        ext z v
        simp [Complex.realScalarOneForm]]
    exact hCorrection_analytic.continuousOn.smul
      (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ)) U)
  have hloopZero_real :
      ∀ {z : ℂ} (γ : Path z z), γ.IsPiecewiseDifferentiable →
        Set.range γ ⊆ U →
          ∫ᶜ w in γ, Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z) w = 0 := by
    intro z γ hγ_piece hγU
    have hzero := hloopZero γ hγ_piece hγU
    rw [show Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z) =
        fun z ↦ (((fun z ↦ logDeriv G z - (n : ℂ) / z) dz) z).restrictScalars ℝ by
        ext z v
        simp [Complex.realScalarOneForm]]
    rw [curveIntegral_restrictScalars]
    exact hzero
  have hPrimitive :
      HasPrimitiveOn U (Complex.realScalarOneForm (fun z ↦ logDeriv G z - (n : ℂ) / z)) :=
    hasPrimitiveOn_of_curveIntegral_eq_zero_loops_of_isOpen_isConnected
      hU_open hU_connected hCorrection_cont hloopZero_real
  have hExact :
      Complex.IsExactOn (fun z ↦ logDeriv G z - (n : ℂ) / z) U := hPrimitive.isExactOn
  rcases hExact with ⟨F, hF_deriv⟩
  have hF_diff :
      DifferentiableOn ℂ F U := fun z hz ↦
        (hF_deriv z hz).differentiableAt.differentiableWithinAt
  refine ⟨F, hF_diff.analyticOnNhd hU_open, ?_⟩
  intro z hz
  exact hF_deriv z hz

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: zero loop integrals for
`logDeriv G - n / z` package into the normal form `c * z^n * exp F` on the punctured ball. -/
lemma puncturedBallNormalForm_of_zeroLoopLogDerivCorrection
    {G : ℂ → ℂ} {ε : ℝ} {n : ℤ}
    (hε : 0 < ε)
    (hG_on : AnalyticOnNhd ℂ G (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hG_analytic : AnalyticOnNhd ℂ (logDeriv G) (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hG_ne : ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), G z ≠ 0)
    (hloopZero :
      ∀ {z : ℂ} (γ : Path z z), γ.IsPiecewiseDifferentiable →
        Set.range γ ⊆ ball (0 : ℂ) ε \ ({0} : Set ℂ) →
          ∫ᶜ w in γ, ((fun z ↦ logDeriv G z - (n : ℂ) / z) dz) w = 0) :
    ∃ F : ℂ → ℂ, ∃ c : ℂ,
      c ≠ 0 ∧
      AnalyticOnNhd ℂ F (ball (0 : ℂ) ε \ ({0} : Set ℂ)) ∧
      EqOn G (fun z ↦ c * (z ^ n) * Complex.exp (F z))
        (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
  let U : Set ℂ := ball (0 : ℂ) ε \ ({0} : Set ℂ)
  have hU_open : IsOpen U := by
    -- The punctured ball stays open, so the logarithmic-derivative comparison applies directly.
    simpa [U, Set.diff_eq] using Metric.isOpen_ball.inter isOpen_ne
  have hU_connected : IsConnected U :=
    (isPathConnected_puncturedBallComplex hε).isConnected
  have hU_preconnected : IsPreconnected U := hU_connected.isPreconnected
  obtain ⟨F, hF_analytic, hF_deriv⟩ :=
    zeroLoopLogDerivPrimitive_onPuncturedBall
      (G := G) (ε := ε) (n := n) hε hG_analytic hloopZero
  let H : ℂ → ℂ := fun z ↦ (z ^ n) * Complex.exp (F z)
  have hH_diff : DifferentiableOn ℂ H U := by
    intro z hz
    -- The model `z^n * exp(F z)` is holomorphic because both factors are.
    have hzpow_diff : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ n) z :=
      (differentiableAt_id : DifferentiableAt ℂ (fun w : ℂ ↦ w) z).zpow (Or.inl hz.2)
    exact (hzpow_diff.mul
      (Complex.differentiableAt_exp.comp z ((hF_deriv z hz).differentiableAt))).differentiableWithinAt
  have hH_ne : ∀ z ∈ U, H z ≠ 0 := by
    intro z hz
    -- On the punctured ball, neither the integer power nor the exponential factor vanishes.
    exact mul_ne_zero (zpow_ne_zero n hz.2) (Complex.exp_ne_zero (F z))
  have hlog_eq : EqOn (logDeriv G) (logDeriv H) U := by
    intro z hz
    have hFz := hF_deriv z hz
    have hzpow_diff : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ n) z :=
      (differentiableAt_id : DifferentiableAt ℂ (fun w : ℂ ↦ w) z).zpow (Or.inl hz.2)
    have hExp_log :
        logDeriv (fun w ↦ Complex.exp (F w)) z = logDeriv G z - (n : ℂ) / z := by
      calc
        logDeriv (fun w ↦ Complex.exp (F w)) z =
            logDeriv Complex.exp (F z) * deriv F z := by
              simpa [Function.comp] using
                logDeriv_comp Complex.differentiableAt_exp (hFz.differentiableAt)
        _ = deriv F z := by simp [Complex.logDeriv_exp]
        _ = logDeriv G z - (n : ℂ) / z := by simpa using hFz.deriv
    have hlog_mul :
        logDeriv (fun w ↦ w ^ n * Complex.exp (F w)) z =
          (n : ℂ) / z + logDeriv (fun w ↦ Complex.exp (F w)) z := by
      have hraw := logDeriv_mul z (zpow_ne_zero n hz.2) (Complex.exp_ne_zero (F z))
        hzpow_diff (Complex.differentiableAt_exp.comp z hFz.differentiableAt)
      change logDeriv (fun w : ℂ ↦ w ^ n * Complex.exp (F w)) z =
        logDeriv (fun w : ℂ ↦ w ^ n) z + logDeriv (Complex.exp ∘ F) z at hraw
      simpa [logDeriv_zpow] using hraw
    calc
      logDeriv G z = (n : ℂ) / z + (logDeriv G z - (n : ℂ) / z) := by ring
      _ = logDeriv (fun w ↦ w ^ n) z + logDeriv (fun w ↦ Complex.exp (F w)) z := by
        rw [logDeriv_zpow, hExp_log]
      _ = logDeriv H z := by
        simpa [H] using hlog_mul.symm
  rcases (logDeriv_eqOn_iff hG_on.differentiableOn hH_diff hU_open hU_preconnected hH_ne hG_ne).mp
      hlog_eq with ⟨c, hc_ne, hc_eq⟩
  refine ⟨F, c, hc_ne, hF_analytic, ?_⟩
  -- Absorb the scalar from `logDeriv_eqOn_iff` into the front coefficient of the normal form.
  simpa [U, H, smul_eq_mul, mul_assoc] using hc_eq

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the dilogarithm power series is
uniformly bounded on the Exercise 16 lens domain by the absolute coefficient sum. -/
lemma dilogarithmPowerSeries_norm_le_exercise16CoeffSum
    {z : ℂ} (hz : z ∈ exercise16Domain) :
    ‖Complex.dilogarithmPowerSeries z‖ ≤ ∑' n : ℕ, ‖exercise16Coeffs n‖ := by
  have hz_norm : ‖z‖ < 1 := by
    simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using hz.1
  have hsum_norm : Summable (fun n : ℕ ↦ ‖exercise16Coeffs n * z ^ (n + 1)‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ summable_exercise16Coeffs.norm
    intro n
    calc
      ‖exercise16Coeffs n * z ^ (n + 1)‖ = ‖exercise16Coeffs n‖ * ‖z ^ (n + 1)‖ := by
        rw [norm_mul]
      _ ≤ ‖exercise16Coeffs n‖ * 1 := by
        gcongr
        have hz_le : ‖z‖ ≤ 1 := le_of_lt hz_norm
        have hp : ‖z‖ ^ (n + 1) ≤ 1 := by
          simpa using pow_le_one₀ (n := n + 1) (norm_nonneg z) hz_le
        simpa [norm_pow] using hp
      _ = ‖exercise16Coeffs n‖ := by ring
  calc
    ‖Complex.dilogarithmPowerSeries z‖ = ‖∑' n : ℕ, exercise16Coeffs n * z ^ (n + 1)‖ := by
      congr 1
      rw [Complex.dilogarithmPowerSeries_eq_tsum]
      apply tsum_congr
      intro n
      simp [exercise16Coeffs, div_eq_mul_inv, mul_comm]
    _ ≤ ∑' n : ℕ, ‖exercise16Coeffs n * z ^ (n + 1)‖ := norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' n : ℕ, ‖exercise16Coeffs n‖ := by
      exact hsum_norm.tsum_le_tsum
        (fun n ↦ by
          calc
            ‖exercise16Coeffs n * z ^ (n + 1)‖ = ‖exercise16Coeffs n‖ * ‖z ^ (n + 1)‖ := by
              rw [norm_mul]
            _ ≤ ‖exercise16Coeffs n‖ * 1 := by
              gcongr
              have hz_le : ‖z‖ ≤ 1 := le_of_lt hz_norm
              have hp : ‖z‖ ^ (n + 1) ≤ 1 := by
                simpa using pow_le_one₀ (n := n + 1) (norm_nonneg z) hz_le
              simpa [norm_pow] using hp
            _ = ‖exercise16Coeffs n‖ := by ring)
        summable_exercise16Coeffs.norm

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the Exercise 16 reflection
identity packages the logarithmic correction into a uniform bound on the lens preimage. -/
lemma exercise16Reflection_logProductBound
    {g : ℂ → ℂ} {E : Set ℂ} {a : ℂ}
    (ha : Exercise16ReflectionConstant a)
    (hE_maps : MapsTo g E exercise16Domain) :
    ∃ M : ℝ, ∀ z ∈ E, ‖Complex.log (g z) * Complex.log (1 - g z)‖ ≤ M := by
  refine ⟨‖a‖ + 2 * (∑' n : ℕ, ‖exercise16Coeffs n‖), ?_⟩
  intro z hz
  have hzE : g z ∈ exercise16Domain := hE_maps hz
  have h1zE : 1 - g z ∈ exercise16Domain := exercise16Domain_one_sub_mem hzE
  have hreflect := ha (g z) hzE
  have hdilog :
      ‖Complex.dilogarithmPowerSeries (g z)‖ ≤ ∑' n : ℕ, ‖exercise16Coeffs n‖ :=
    dilogarithmPowerSeries_norm_le_exercise16CoeffSum hzE
  have hOneSub_dilog :
      ‖Complex.dilogarithmPowerSeries (1 - g z)‖ ≤ ∑' n : ℕ, ‖exercise16Coeffs n‖ :=
    dilogarithmPowerSeries_norm_le_exercise16CoeffSum h1zE
  have hrewrite :
      a - Complex.dilogarithmPowerSeries (g z) -
          Complex.dilogarithmPowerSeries (1 - g z) =
        Complex.log (g z) * Complex.log (1 - g z) := by
    calc
      a - Complex.dilogarithmPowerSeries (g z) -
          Complex.dilogarithmPowerSeries (1 - g z) =
        a - (Complex.dilogarithmPowerSeries (g z) +
          Complex.dilogarithmPowerSeries (1 - g z)) := by ring
      _ = a - (a - Complex.log (g z) * Complex.log (1 - g z)) := by rw [hreflect]
      _ = Complex.log (g z) * Complex.log (1 - g z) := by ring
  calc
    ‖Complex.log (g z) * Complex.log (1 - g z)‖ =
        ‖a - Complex.dilogarithmPowerSeries (g z) -
          Complex.dilogarithmPowerSeries (1 - g z)‖ := by
            rw [hrewrite]
    _ ≤ ‖a‖ + ‖-Complex.dilogarithmPowerSeries (g z) + -Complex.dilogarithmPowerSeries (1 - g z)‖ := by
          simpa [sub_eq_add_neg, add_assoc] using
            norm_add_le a (-Complex.dilogarithmPowerSeries (g z) +
              -Complex.dilogarithmPowerSeries (1 - g z))
    _ ≤ ‖a‖ + (‖-Complex.dilogarithmPowerSeries (g z)‖ +
          ‖-Complex.dilogarithmPowerSeries (1 - g z)‖) := by
            gcongr
            exact norm_add_le _ _
    _ = ‖a‖ + (‖Complex.dilogarithmPowerSeries (g z)‖ +
          ‖Complex.dilogarithmPowerSeries (1 - g z)‖) := by simp
    _ ≤ ‖a‖ + (∑' n : ℕ, ‖exercise16Coeffs n‖ + ∑' n : ℕ, ‖exercise16Coeffs n‖) := by
          gcongr
    _ = ‖a‖ + 2 * (∑' n : ℕ, ‖exercise16Coeffs n‖) := by ring

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: once a value leaves the
Exercise 16 lens domain, at least one of the reciprocals `w⁻¹` or `(1 - w)⁻¹` already has norm
at most `1`. -/
lemma reciprocalNorm_le_one_of_not_mem_exercise16Domain
    {w : ℂ} (hw : w ∉ exercise16Domain) :
    ‖w⁻¹‖ ≤ 1 ∨ ‖(1 - w)⁻¹‖ ≤ 1 := by
  by_cases hw_ball : ‖w‖ < 1
  · right
    have hnot_ball : ¬ ‖w - 1‖ < 1 := by
      intro hw_one
      apply hw
      constructor
      · simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using hw_ball
      · simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using hw_one
    have hnorm_eq : ‖1 - w‖ = ‖w - 1‖ := by
      simpa [sub_eq_add_neg] using norm_sub_rev (1 : ℂ) w
    have hnorm_ge : 1 ≤ ‖1 - w‖ := by
      have hnot : ¬ ‖1 - w‖ < 1 := by
        intro hlt
        apply hnot_ball
        rw [← hnorm_eq]
        exact hlt
      exact le_of_not_gt hnot
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hnorm_ge
  · left
    have hnorm_ge : 1 ≤ ‖w‖ := le_of_not_gt hw_ball
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hnorm_ge

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the reflection-bound estimate
on `Complex.log g * Complex.log (1 - g)` yields the reciprocal-log product bound actually used in
the Picard endgame. -/
lemma reciprocalLogProductBound_of_exercise16Preimage
    {g : ℂ → ℂ} {E : Set ℂ} {M : ℝ}
    (hE_maps : MapsTo g E exercise16Domain)
    (hbound : ∀ z ∈ E, ‖Complex.log (g z) * Complex.log (1 - g z)‖ ≤ M) :
    ∀ z ∈ E, Real.log ‖(g z)⁻¹‖ * Real.log ‖((1 - g z)⁻¹)‖ ≤ M := by
  intro z hz
  have hzE : g z ∈ exercise16Domain := hE_maps hz
  have hg_norm_lt : ‖g z‖ < 1 := by
    simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using hzE.1
  have hone_sub_norm_lt : ‖1 - g z‖ < 1 := by
    have hgz_one_lt : ‖g z - 1‖ < 1 := by
      simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using hzE.2
    have hnorm_eq : ‖1 - g z‖ = ‖g z - 1‖ := by
      simpa [sub_eq_add_neg] using norm_sub_rev (1 : ℂ) (g z)
    rw [hnorm_eq]
    exact hgz_one_lt
  have hg_ne : g z ≠ 0 := by
    intro hgz
    have : ¬ ‖(0 : ℂ) - 1‖ < 1 := by norm_num
    exact this (by simpa [hgz] using hzE.2)
  have hone_sub_ne : 1 - g z ≠ 0 := by
    intro h1gz
    have hg_one : g z = 1 := (sub_eq_zero.mp h1gz).symm
    have : ¬ ‖(1 : ℂ)‖ < 1 := by norm_num
    exact this (by simpa [hg_one] using hzE.1)
  have hg_log_eq : Real.log ‖(g z)⁻¹‖ = -(Complex.log (g z)).re := by
    calc
      Real.log ‖(g z)⁻¹‖ = Real.log (‖g z‖⁻¹) := by rw [norm_inv]
      _ = -Real.log ‖g z‖ := by rw [Real.log_inv]
      _ = -(Complex.log (g z)).re := by rw [Complex.log_re]
  have hone_sub_log_eq :
      Real.log ‖((1 - g z)⁻¹)‖ = -(Complex.log (1 - g z)).re := by
    calc
      Real.log ‖((1 - g z)⁻¹)‖ = Real.log (‖1 - g z‖⁻¹) := by rw [norm_inv]
      _ = -Real.log ‖1 - g z‖ := by rw [Real.log_inv]
      _ = -(Complex.log (1 - g z)).re := by rw [Complex.log_re]
  have hg_log_nonneg : 0 ≤ Real.log ‖(g z)⁻¹‖ := by
    rw [norm_inv]
    exact Real.log_nonneg <| (one_le_inv₀ (norm_pos_iff.mpr hg_ne)).2 hg_norm_lt.le
  have hone_sub_log_nonneg : 0 ≤ Real.log ‖((1 - g z)⁻¹)‖ := by
    rw [norm_inv]
    exact Real.log_nonneg <| (one_le_inv₀ (norm_pos_iff.mpr hone_sub_ne)).2 hone_sub_norm_lt.le
  have hg_log_le : Real.log ‖(g z)⁻¹‖ ≤ ‖Complex.log (g z)‖ := by
    have hre_nonpos : (Complex.log (g z)).re ≤ 0 := by
      rw [Complex.log_re]
      exact Real.log_nonpos (norm_nonneg _) hg_norm_lt.le
    calc
      Real.log ‖(g z)⁻¹‖ = -(Complex.log (g z)).re := hg_log_eq
      _ = |(Complex.log (g z)).re| := by rw [abs_of_nonpos hre_nonpos]
      _ ≤ ‖Complex.log (g z)‖ := Complex.abs_re_le_norm _
  have hone_sub_log_le : Real.log ‖((1 - g z)⁻¹)‖ ≤ ‖Complex.log (1 - g z)‖ := by
    have hre_nonpos : (Complex.log (1 - g z)).re ≤ 0 := by
      rw [Complex.log_re]
      exact Real.log_nonpos (norm_nonneg _) hone_sub_norm_lt.le
    calc
      Real.log ‖((1 - g z)⁻¹)‖ = -(Complex.log (1 - g z)).re := hone_sub_log_eq
      _ = |(Complex.log (1 - g z)).re| := by rw [abs_of_nonpos hre_nonpos]
      _ ≤ ‖Complex.log (1 - g z)‖ := Complex.abs_re_le_norm _
  calc
    Real.log ‖(g z)⁻¹‖ * Real.log ‖((1 - g z)⁻¹)‖
        ≤ ‖Complex.log (g z)‖ * ‖Complex.log (1 - g z)‖ := by
          exact mul_le_mul hg_log_le hone_sub_log_le hone_sub_log_nonneg (norm_nonneg _)
    _ = ‖Complex.log (g z) * Complex.log (1 - g z)‖ := by rw [norm_mul]
    _ ≤ M := hbound z hz

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: on the Exercise 16 preimage,
the reciprocal-log product bound already gives a uniform pointwise bound for at least one
reciprocal branch. -/
lemma reciprocalPointwiseBound_of_exercise16LogProduct
    {g : ℂ → ℂ} {E : Set ℂ} {M : ℝ}
    (hE_maps : MapsTo g E exercise16Domain)
    (hbound : ∀ z ∈ E, Real.log ‖(g z)⁻¹‖ * Real.log ‖((1 - g z)⁻¹)‖ ≤ M) :
    ∀ z ∈ E,
      ‖(g z)⁻¹‖ ≤ Real.exp (max M 1) ∨ ‖((1 - g z)⁻¹)‖ ≤ Real.exp (max M 1) := by
  intro z hz
  let T : ℝ := max M 1
  have hzE : g z ∈ exercise16Domain := hE_maps hz
  have hg_norm_lt : ‖g z‖ < 1 := by
    simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using hzE.1
  have hone_sub_norm_lt : ‖1 - g z‖ < 1 := by
    have hgz_one_lt : ‖g z - 1‖ < 1 := by
      simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using hzE.2
    have hnorm_eq : ‖1 - g z‖ = ‖g z - 1‖ := by
      simpa [sub_eq_add_neg] using norm_sub_rev (1 : ℂ) (g z)
    rw [hnorm_eq]
    exact hgz_one_lt
  have hg_ne : g z ≠ 0 := by
    intro hgz
    have : ¬ ‖(0 : ℂ) - 1‖ < 1 := by norm_num
    exact this (by simpa [hgz] using hzE.2)
  have hone_sub_ne : 1 - g z ≠ 0 := by
    intro h1gz
    have hg_one : g z = 1 := (sub_eq_zero.mp h1gz).symm
    have : ¬ ‖(1 : ℂ)‖ < 1 := by norm_num
    exact this (by simpa [hg_one] using hzE.1)
  have hx_nonneg : 0 ≤ Real.log ‖(g z)⁻¹‖ := by
    rw [norm_inv]
    exact Real.log_nonneg <| (one_le_inv₀ (norm_pos_iff.mpr hg_ne)).2 hg_norm_lt.le
  have hy_nonneg : 0 ≤ Real.log ‖((1 - g z)⁻¹)‖ := by
    rw [norm_inv]
    exact Real.log_nonneg <| (one_le_inv₀ (norm_pos_iff.mpr hone_sub_ne)).2 hone_sub_norm_lt.le
  have hT_ge_one : 1 ≤ T := by
    dsimp [T]
    exact le_max_right M 1
  have hT_nonneg : 0 ≤ T := by
    exact le_trans (by norm_num) hT_ge_one
  have hT_sq_ge_M : M ≤ T * T := by
    have hT_mul : T ≤ T * T := by
      nlinarith
    exact le_trans (by
      dsimp [T]
      exact le_max_left M 1) hT_mul
  by_cases hx : Real.log ‖(g z)⁻¹‖ ≤ T
  · left
    have hnorm_pos : 0 < ‖(g z)⁻¹‖ := by
      exact norm_pos_iff.mpr (inv_ne_zero hg_ne)
    exact (Real.log_le_iff_le_exp hnorm_pos).1 hx
  · right
    have hx_gt : T < Real.log ‖(g z)⁻¹‖ := lt_of_not_ge hx
    have hy_le : Real.log ‖((1 - g z)⁻¹)‖ ≤ T := by
      by_contra hy
      have hy_gt : T < Real.log ‖((1 - g z)⁻¹)‖ := lt_of_not_ge hy
      have hTT_lt :
          T * T <
            Real.log ‖(g z)⁻¹‖ * Real.log ‖((1 - g z)⁻¹)‖ := by
        nlinarith
      have hM_lt : M <
          Real.log ‖(g z)⁻¹‖ * Real.log ‖((1 - g z)⁻¹)‖ := by
        exact lt_of_le_of_lt hT_sq_ge_M hTT_lt
      exact not_lt_of_ge (hbound z hz) hM_lt
    have hnorm_pos : 0 < ‖((1 - g z)⁻¹)‖ := by
      exact norm_pos_iff.mpr (inv_ne_zero hone_sub_ne)
    exact (Real.log_le_iff_le_exp hnorm_pos).1 hy_le

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the quotient selector
`Real.log ‖a / b‖` is the difference of the two reciprocal logarithms. -/
lemma log_norm_div_eq_reciprocalLogDiff {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.log ‖a / b‖ = Real.log ‖b⁻¹‖ - Real.log ‖a⁻¹‖ := by
  -- Rewrite the quotient norm logarithm as `log ‖a‖ - log ‖b‖`, then translate to reciprocals.
  have hdiv : Real.log ‖a / b‖ = Real.log ‖a‖ - Real.log ‖b‖ := by
    simpa [norm_div] using
      (Real.log_div (show ‖a‖ ≠ 0 by exact norm_ne_zero_iff.mpr ha)
        (show ‖b‖ ≠ 0 by exact norm_ne_zero_iff.mpr hb))
  rw [hdiv]
  rw [norm_inv, norm_inv, Real.log_inv, Real.log_inv]
  ring

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if the quotient selector is
nonnegative and one reciprocal branch is bounded by `K`, then the `g⁻¹` branch is bounded by the
same `K`. -/
lemma reciprocalBound_of_logQuotientNonneg
    {g : ℂ → ℂ} {z : ℂ} {K : ℝ}
    (h0 : g z ≠ 0) (h1 : 1 - g z ≠ 0)
    (hbranch : ‖(g z)⁻¹‖ ≤ K ∨ ‖((1 - g z)⁻¹)‖ ≤ K)
    (hv : 0 ≤ Real.log ‖g z / (1 - g z)‖) :
    ‖(g z)⁻¹‖ ≤ K := by
  rcases hbranch with hgK | hOneSubK
  · exact hgK
  · -- A nonnegative selector means `‖g z / (1 - g z)‖ ≥ 1`, hence `‖(g z)⁻¹‖ ≤ ‖((1 - g z)⁻¹)‖`.
    have hqpos : 0 < ‖g z / (1 - g z)‖ := by
      exact norm_pos_iff.mpr (div_ne_zero h0 h1)
    have hq_ge_one : 1 ≤ ‖g z / (1 - g z)‖ :=
      (Real.log_nonneg_iff hqpos).1 hv
    have hnorm : ‖1 - g z‖ ≤ ‖g z‖ := by
      rw [norm_div] at hq_ge_one
      exact (one_le_div₀ (norm_pos_iff.mpr h1)).mp hq_ge_one
    have hinv : ‖(g z)⁻¹‖ ≤ ‖((1 - g z)⁻¹)‖ := by
      rw [norm_inv, norm_inv]
      exact (inv_le_inv₀ (norm_pos_iff.mpr h0) (norm_pos_iff.mpr h1)).2 hnorm
    exact le_trans hinv hOneSubK

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if the quotient selector is
nonpositive and one reciprocal branch is bounded by `K`, then the `(1 - g)⁻¹` branch is bounded by
the same `K`. -/
lemma reciprocalBound_of_logQuotientNonpos
    {g : ℂ → ℂ} {z : ℂ} {K : ℝ}
    (h0 : g z ≠ 0) (h1 : 1 - g z ≠ 0)
    (hbranch : ‖(g z)⁻¹‖ ≤ K ∨ ‖((1 - g z)⁻¹)‖ ≤ K)
    (hv : Real.log ‖g z / (1 - g z)‖ ≤ 0) :
    ‖((1 - g z)⁻¹)‖ ≤ K := by
  rcases hbranch with hgK | hOneSubK
  · -- A nonpositive selector means `‖g z / (1 - g z)‖ ≤ 1`, so the reciprocal inequality reverses.
    have hq_le_one : ‖g z / (1 - g z)‖ ≤ 1 := by
      have hq_nonneg : 0 ≤ ‖g z / (1 - g z)‖ := norm_nonneg _
      exact (Real.log_nonpos_iff hq_nonneg).1 hv
    have hnorm : ‖g z‖ ≤ ‖1 - g z‖ := by
      rw [norm_div] at hq_le_one
      exact (div_le_one₀ (norm_pos_iff.mpr h1)).1 hq_le_one
    have hinv : ‖((1 - g z)⁻¹)‖ ≤ ‖(g z)⁻¹‖ := by
      rw [norm_inv, norm_inv]
      exact (inv_le_inv₀ (norm_pos_iff.mpr h1) (norm_pos_iff.mpr h0)).2 hnorm
    exact le_trans hinv hgK
  · exact hOneSubK

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if the quotient selector
vanishes, then any pointwise reciprocal-branch bound already bounds both branches. -/
lemma reciprocalBounds_of_logQuotientEqZero
    {g : ℂ → ℂ} {z : ℂ} {K : ℝ}
    (h0 : g z ≠ 0) (h1 : 1 - g z ≠ 0)
    (hbranch : ‖(g z)⁻¹‖ ≤ K ∨ ‖((1 - g z)⁻¹)‖ ≤ K)
    (hv : Real.log ‖g z / (1 - g z)‖ = 0) :
    ‖(g z)⁻¹‖ ≤ K ∧ ‖((1 - g z)⁻¹)‖ ≤ K := by
  constructor
  · -- Reuse the nonnegative selector case after rewriting `v = 0`.
    exact reciprocalBound_of_logQuotientNonneg h0 h1 hbranch <| by rw [hv]
  · -- The nonpositive selector case is the same rewrite.
    exact reciprocalBound_of_logQuotientNonpos h0 h1 hbranch <| by rw [hv]

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if the reciprocal of `g z`
already exceeds the common threshold `K`, then the quotient selector must be negative. -/
lemma selectorNegOfLargeReciprocal
    {g : ℂ → ℂ} {z : ℂ} {K : ℝ}
    (h0 : g z ≠ 0) (h1 : 1 - g z ≠ 0)
    (hbranch : ‖(g z)⁻¹‖ ≤ K ∨ ‖((1 - g z)⁻¹)‖ ≤ K)
    (hlarge : K < ‖(g z)⁻¹‖) :
    Real.log ‖g z / (1 - g z)‖ < 0 := by
  -- A nonnegative selector would force the `g⁻¹` branch back below `K`, contradicting
  -- the assumed large reciprocal.
  by_contra hv
  have hv_nonneg : 0 ≤ Real.log ‖g z / (1 - g z)‖ := le_of_not_gt hv
  exact not_lt_of_ge (reciprocalBound_of_logQuotientNonneg h0 h1 hbranch hv_nonneg) hlarge

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if the reciprocal of
`1 - g z` already exceeds the common threshold `K`, then the quotient selector must be positive. -/
lemma selectorPosOfLargeOneSubReciprocal
    {g : ℂ → ℂ} {z : ℂ} {K : ℝ}
    (h0 : g z ≠ 0) (h1 : 1 - g z ≠ 0)
    (hbranch : ‖(g z)⁻¹‖ ≤ K ∨ ‖((1 - g z)⁻¹)‖ ≤ K)
    (hlarge : K < ‖((1 - g z)⁻¹)‖) :
    0 < Real.log ‖g z / (1 - g z)‖ := by
  -- A nonpositive selector would force the `(1 - g)⁻¹` branch back below `K`, contradicting
  -- the assumed large reciprocal.
  by_contra hv
  have hv_nonpos : Real.log ‖g z / (1 - g z)‖ ≤ 0 := le_of_not_gt hv
  exact not_lt_of_ge (reciprocalBound_of_logQuotientNonpos h0 h1 hbranch hv_nonpos) hlarge

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if one point in a punctured
ball violates the `g⁻¹` bound and another violates the `(1 - g)⁻¹` bound, then the quotient
selector vanishes somewhere in that same punctured ball. -/
lemma mixedLargeBranchesHaveZeroSelector
    {g : ℂ → ℂ} {δ K : ℝ} {zNeg zPos : ℂ}
    (hδ : 0 < δ)
    (hzNeg : zNeg ∈ ball (0 : ℂ) δ \ ({0} : Set ℂ))
    (hzPos : zPos ∈ ball (0 : ℂ) δ \ ({0} : Set ℂ))
    (hbranch :
      ∀ z ∈ ball (0 : ℂ) δ \ ({0} : Set ℂ),
        ‖(g z)⁻¹‖ ≤ K ∨ ‖((1 - g z)⁻¹)‖ ≤ K)
    (hg_nonzero : ∀ z ∈ ball (0 : ℂ) δ \ ({0} : Set ℂ), g z ≠ 0)
    (hone_sub_nonzero : ∀ z ∈ ball (0 : ℂ) δ \ ({0} : Set ℂ), 1 - g z ≠ 0)
    (hv_cont :
      ContinuousOn (fun z ↦ Real.log ‖g z / (1 - g z)‖) (ball (0 : ℂ) δ \ ({0} : Set ℂ)))
    (hzNegLarge : K < ‖(g zNeg)⁻¹‖)
    (hzPosLarge : K < ‖((1 - g zPos)⁻¹)‖) :
    ∃ w ∈ ball (0 : ℂ) δ \ ({0} : Set ℂ), Real.log ‖g w / (1 - g w)‖ = 0 := by
  let s : Set ℂ := ball (0 : ℂ) δ \ ({0} : Set ℂ)
  have hvneg : Real.log ‖g zNeg / (1 - g zNeg)‖ < 0 := by
    -- Turn the failed `g⁻¹` bound into a strict negative selector value.
    exact selectorNegOfLargeReciprocal (hg_nonzero zNeg hzNeg) (hone_sub_nonzero zNeg hzNeg)
      (hbranch zNeg hzNeg) hzNegLarge
  have hvpos : 0 < Real.log ‖g zPos / (1 - g zPos)‖ := by
    -- The failed `(1 - g)⁻¹` bound produces the opposite strict sign.
    exact selectorPosOfLargeOneSubReciprocal (hg_nonzero zPos hzPos) (hone_sub_nonzero zPos hzPos)
      (hbranch zPos hzPos) hzPosLarge
  have hs_preconnected : IsPreconnected s := by
    -- The punctured ball is path connected, hence preconnected.
    simpa [s] using (isPathConnected_puncturedBallComplex hδ).isConnected.isPreconnected
  have hzero_mem :
      (0 : ℝ) ∈
        Set.Icc (Real.log ‖g zNeg / (1 - g zNeg)‖) (Real.log ‖g zPos / (1 - g zPos)‖) := by
    exact ⟨le_of_lt hvneg, le_of_lt hvpos⟩
  have hzero_image :
      (0 : ℝ) ∈ (fun z ↦ Real.log ‖g z / (1 - g z)‖) '' s := by
    exact hs_preconnected.intermediate_value hzNeg hzPos hv_cont hzero_mem
  rcases hzero_image with ⟨w, hw, hw0⟩
  exact ⟨w, hw, hw0⟩

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: on a punctured ball where `g`
omits `0` and `1`, the two reciprocal norm functions are continuous. -/
lemma reciprocalNorms_continuousOn_puncturedBall
    {g : ℂ → ℂ} {ε : ℝ}
    (hg_analytic : AnalyticOnNhd ℂ g (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (h0 : 0 ∉ g '' (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (h1 : 1 ∉ g '' (ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    ContinuousOn (fun z ↦ ‖(g z)⁻¹‖) (ball (0 : ℂ) ε \ ({0} : Set ℂ)) ∧
      ContinuousOn (fun z ↦ ‖((1 - g z)⁻¹)‖) (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
  let U : Set ℂ := ball (0 : ℂ) ε \ ({0} : Set ℂ)
  have hg_cont : ContinuousOn g U := hg_analytic.continuousOn
  have hg_nonzero : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz hgz0
    exact h0 ⟨z, hz, hgz0⟩
  have hone_sub_cont : ContinuousOn (fun z ↦ 1 - g z) U := by
    simpa [U] using continuousOn_const.sub hg_cont
  have hone_sub_nonzero : ∀ z ∈ U, 1 - g z ≠ 0 := by
    intro z hz hz1
    exact h1 ⟨z, hz, (sub_eq_zero.mp hz1).symm⟩
  constructor
  · -- Inversion is continuous away from the omitted value `0`.
    simpa [U] using (hg_cont.inv₀ hg_nonzero).norm
  · -- The same argument applies to the omitted value `1`.
    simpa [U] using (hone_sub_cont.inv₀ hone_sub_nonzero).norm

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: a continuous real-valued
function that is at most `K` at a point stays below any larger bound on a small neighborhood of
that point. -/
lemma locally_le_of_continuousAt_of_lt
    {f : ℂ → ℝ} {z₀ : ℂ} {K B : ℝ}
    (hcont : ContinuousAt f z₀) (hz₀ : f z₀ ≤ K) (hKB : K < B) :
    ∃ r > 0, ∀ z : ℂ, dist z z₀ < r → f z ≤ B := by
  rcases (Metric.continuousAt_iff.mp hcont) (B - K) (sub_pos.mpr hKB) with ⟨r, hr, hrule⟩
  refine ⟨r, hr, ?_⟩
  intro z hz
  have hdist : dist (f z) (f z₀) < B - K := hrule hz
  have habs : |f z - f z₀| < B - K := by
    simpa [Real.dist_eq] using hdist
  have hupper : f z - f z₀ < B - K := (abs_lt.mp habs).2
  linarith

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the quotient selector
`z ↦ Real.log ‖g z / (1 - g z)‖` is continuous on the punctured ball where `g` omits `0` and `1`.
-/
lemma logQuotientSelector_continuousOn
    {g : ℂ → ℂ} {ε : ℝ}
    (hg_analytic : AnalyticOnNhd ℂ g (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (h0 : 0 ∉ g '' (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (h1 : 1 ∉ g '' (ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    ContinuousOn (fun z ↦ Real.log ‖g z / (1 - g z)‖) (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
  let U : Set ℂ := ball (0 : ℂ) ε \ ({0} : Set ℂ)
  have hg_cont : ContinuousOn g U := hg_analytic.continuousOn
  have hone_sub_cont : ContinuousOn (fun z ↦ 1 - g z) U := by
    simpa [U] using (analyticOnNhd_const.sub hg_analytic).continuousOn
  have hquot_cont : ContinuousOn (fun z ↦ g z / (1 - g z)) U := by
    -- The quotient is continuous because `1 - g` never vanishes on the punctured ball.
    refine ContinuousOn.div hg_cont hone_sub_cont ?_
    intro z hz hz1
    exact h1 ⟨z, by simpa [U] using hz, (sub_eq_zero.mp hz1).symm⟩
  have hnorm_cont : ContinuousOn (fun z ↦ ‖g z / (1 - g z)‖) U := by
    simpa using hquot_cont.norm
  have hnorm_ne : ∀ z ∈ U, ‖g z / (1 - g z)‖ ≠ 0 := by
    intro z hz
    have hgz0 : g z ≠ 0 := by
      intro hgz0
      exact h0 ⟨z, by simpa [U] using hz, hgz0⟩
    have hone_sub_ne : 1 - g z ≠ 0 := by
      intro hz1
      exact h1 ⟨z, by simpa [U] using hz, (sub_eq_zero.mp hz1).symm⟩
    exact norm_ne_zero_iff.mpr (div_ne_zero hgz0 hone_sub_ne)
  -- Compose the continuous quotient norm with the owner continuity of `Real.log` away from `0`.
  exact Real.continuousOn_log.comp hnorm_cont hnorm_ne

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: an eventual bound for `g⁻¹` on
the punctured neighborhood makes `g` meromorphic at `0`. -/
lemma meromorphicAt_of_eventually_bounded_inv
    {g : ℂ → ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (hg_analytic : AnalyticOnNhd ℂ g (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (h0 : 0 ∉ g '' (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hbound : ∃ M : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖(g z)⁻¹‖ ≤ M) :
    MeromorphicAt g 0 := by
  let h : ℂ → ℂ := fun z ↦ (g z)⁻¹
  have hh_nonzero :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), g z ≠ 0 := by
    intro z hz hz0
    exact h0 ⟨z, hz, hz0⟩
  have hh_analytic : AnalyticOnNhd ℂ h (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
    -- The reciprocal is analytic on the punctured ball because `g` omits `0` there.
    simpa [h, Pi.inv_apply] using hg_analytic.inv hh_nonzero
  obtain ⟨ĥ, hĥ_analytic, hh_eq⟩ :=
    (exists_analytic_extension_at_zero_iff_eventually_bounded_norm
      (f := h) (r := ε) hε hh_analytic).2 hbound
  have hh_meromorphic : MeromorphicAt h 0 := by
    -- Proposition 4.1 turns the eventual punctured-neighborhood bound into a removable extension.
    exact hĥ_analytic.meromorphicAt.congr hh_eq.symm
  have hg_inv_inv_meromorphic : MeromorphicAt (fun z ↦ ((g z)⁻¹)⁻¹) 0 := by
    -- Invert the removable reciprocal before collapsing the double inversion pointwise.
    convert (MeromorphicAt.inv (f := h) (x := 0) hh_meromorphic) using 1
  -- Inverting the removable reciprocal recovers meromorphicity of the original map.
  exact hg_inv_inv_meromorphic.congr <| Filter.Eventually.of_forall fun z ↦ by simp

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: an eventual bound for
`(1 - g)⁻¹` on the punctured neighborhood makes `g` meromorphic at `0`. -/
lemma meromorphicAt_of_eventually_bounded_one_sub_inv
    {g : ℂ → ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (hg_analytic : AnalyticOnNhd ℂ g (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (h1 : 1 ∉ g '' (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hbound : ∃ M : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖((1 - g z)⁻¹)‖ ≤ M) :
    MeromorphicAt g 0 := by
  let h : ℂ → ℂ := fun z ↦ ((1 - g z)⁻¹)
  have hone_sub_analytic :
      AnalyticOnNhd ℂ (fun z ↦ 1 - g z) (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
    -- The omitted-value transform `1 - g` is analytic on the same punctured ball.
    simpa using analyticOnNhd_const.sub hg_analytic
  have hh_nonzero :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), 1 - g z ≠ 0 := by
    intro z hz hz1
    exact h1 ⟨z, hz, (sub_eq_zero.mp hz1).symm⟩
  have hh_analytic : AnalyticOnNhd ℂ h (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
    -- The reciprocal of `1 - g` is analytic because `g` omits `1`.
    simpa [h, Pi.inv_apply] using hone_sub_analytic.inv hh_nonzero
  obtain ⟨ĥ, hĥ_analytic, hh_eq⟩ :=
    (exists_analytic_extension_at_zero_iff_eventually_bounded_norm
      (f := h) (r := ε) hε hh_analytic).2 hbound
  have hh_meromorphic : MeromorphicAt h 0 := by
    -- Proposition 4.1 again yields a removable extension of the bounded reciprocal branch.
    exact hĥ_analytic.meromorphicAt.congr hh_eq.symm
  have hone_sub_inv_inv_meromorphic : MeromorphicAt (fun z ↦ (((1 - g z)⁻¹)⁻¹)) 0 := by
    -- Invert the removable reciprocal branch before simplifying the pointwise double inversion.
    convert (MeromorphicAt.inv (f := h) (x := 0) hh_meromorphic) using 1
  have hone_sub_meromorphic : MeromorphicAt (fun z ↦ 1 - g z) 0 := by
    -- Inverting the reciprocal branch recovers meromorphicity of `1 - g`.
    exact hone_sub_inv_inv_meromorphic.congr <| Filter.Eventually.of_forall fun z ↦ by simp
  -- Subtract the meromorphic branch from the constant `1` to recover `g`.
  exact
    (MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt₁
      (f := fun _ : ℂ ↦ 1) (g := g) (x := 0) (MeromorphicAt.const 1 0)).mp <| by
        simpa using hone_sub_meromorphic

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: once one reciprocal branch is
eventually bounded near `0`, the omitted-value map is meromorphic at the center. -/
lemma meromorphicAt_of_eventually_bounded_reciprocal_branch
    {g : ℂ → ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (hg_analytic : AnalyticOnNhd ℂ g (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (h0 : 0 ∉ g '' (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (h1 : 1 ∉ g '' (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hbranch :
      (∃ M : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖(g z)⁻¹‖ ≤ M) ∨
        ∃ M : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖((1 - g z)⁻¹)‖ ≤ M) :
    MeromorphicAt g 0 := by
  rcases hbranch with hinv | hone_sub_inv
  · -- The `g⁻¹` branch is the direct Proposition 4.1 route.
    exact meromorphicAt_of_eventually_bounded_inv hε hg_analytic h0 hinv
  · -- Otherwise use the bounded reciprocal of `1 - g` and subtract from the constant `1`.
    exact meromorphicAt_of_eventually_bounded_one_sub_inv hε hg_analytic h1 hone_sub_inv

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: a uniform bound for one
reciprocal branch on a concrete punctured ball already yields the eventual filter-level branch
bound needed by the meromorphicity criterion. -/
lemma eventuallyBoundedReciprocalBranch_of_puncturedBallBound
    {g : ℂ → ℂ} {δ M : ℝ}
    (hδ : 0 < δ)
    (hbound :
      (∀ z ∈ ball (0 : ℂ) δ \ ({0} : Set ℂ), ‖(g z)⁻¹‖ ≤ M) ∨
        ∀ z ∈ ball (0 : ℂ) δ \ ({0} : Set ℂ), ‖((1 - g z)⁻¹)‖ ≤ M) :
    (∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖(g z)⁻¹‖ ≤ B) ∨
      ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖((1 - g z)⁻¹)‖ ≤ B := by
  rcases hbound with hginv | honeSubInv
  · left
    refine ⟨M, ?_⟩
    have hball : ball (0 : ℂ) δ \ ({0} : Set ℂ) ∈ 𝓝[≠] (0 : ℂ) := by
      -- Rewrite the punctured ball as the standard punctured-neighborhood basis element.
      rw [show ball (0 : ℂ) δ \ ({0} : Set ℂ) = ball (0 : ℂ) δ ∩ ({(0 : ℂ)}ᶜ) by
        ext z
        simp [Set.diff_eq]]
      exact Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, subset_rfl⟩
    exact Filter.mem_of_superset hball hginv
  · right
    refine ⟨M, ?_⟩
    have hball : ball (0 : ℂ) δ \ ({0} : Set ℂ) ∈ 𝓝[≠] (0 : ℂ) := by
      -- The same punctured-ball basis element packages the `(1 - g)⁻¹` branch bound.
      rw [show ball (0 : ℂ) δ \ ({0} : Set ℂ) = ball (0 : ℂ) δ ∩ ({(0 : ℂ)}ᶜ) by
        ext z
        simp [Set.diff_eq]]
      exact Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, subset_rfl⟩
    exact Filter.mem_of_superset hball honeSubInv

