import DifferentialForms_Cartan_1970.I.section02.«0010_Proposition_5_1»
import DifferentialForms_Cartan_1970.I.section02.«0016_Proposition_9_1»
import DifferentialForms_Cartan_1970.IV.section13.«0001_Definition_IV_1_extra_1»
import DifferentialForms_Cartan_1970.IV.section13.«0007_Proposition_3_I»
import DifferentialForms_Cartan_1970.VII.section27.«0001_Theorem_I».Index
import Mathlib

open Filter
open Set
open scoped Topology BigOperators MvPowerSeries PowerSeries
open PowerSeries

/-- Helper for Theorem I: translating the vector variable by the initial value `b` produces the
correct recentered multilinear power-series germ at `(0, 0)`, still defined on a small ball sent
into `Ω`. -/
private theorem recentered_rhs_hasFPowerSeriesAt {n : ℕ}
    {Ω : Set (ℂ × (Fin n → ℂ))} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ} {b : Fin n → ℂ}
    (hΩ : IsOpen Ω) (h0 : ((0 : ℂ), b) ∈ Ω)
    (hf : AnalyticOnNhd ℂ (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 p.2) Ω) :
    ∃ Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ),
      HasFPowerSeriesAt (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 (b + p.2)) Q (0, 0) ∧
      ∃ r : ℝ, 0 < r ∧
        MapsTo (fun p : ℂ × (Fin n → ℂ) ↦ (p.1, b + p.2))
          (Metric.ball (0 : ℂ × (Fin n → ℂ)) r) Ω := by
  -- First record that the translation `(z, u) ↦ (z, b + u)` is analytic at the recentered origin.
  have htranslate_analytic :
      AnalyticAt ℂ (fun p : ℂ × (Fin n → ℂ) ↦ (p.1, b + p.2))
        ((0 : ℂ), (0 : Fin n → ℂ)) := by
    exact analyticAt_fst.prod (analyticAt_const.add analyticAt_snd)
  -- Composing the original analytic germ with that translation gives the recentered analytic germ.
  have hrecentered_analytic :
      AnalyticAt ℂ (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 (b + p.2))
        ((0 : ℂ), (0 : Fin n → ℂ)) := by
    have htranslate_zero :
        (fun p : ℂ × (Fin n → ℂ) ↦ (p.1, b + p.2)) ((0 : ℂ), (0 : Fin n → ℂ)) = ((0 : ℂ), b) := by
      simp
    exact (hf ((0 : ℂ), b) h0).comp_of_eq htranslate_analytic htranslate_zero
  obtain ⟨Q, hQ⟩ := hrecentered_analytic
  -- Openness of `Ω` and continuity of the translation leave a small product ball inside `Ω`.
  have htranslate_nhds :
      (fun p : ℂ × (Fin n → ℂ) ↦ (p.1, b + p.2)) ⁻¹' Ω ∈ 𝓝 (0 : ℂ × (Fin n → ℂ)) := by
    exact htranslate_analytic.continuousAt.preimage_mem_nhds <| by
      simpa using (hΩ.mem_nhds h0)
  rcases Metric.mem_nhds_iff.mp htranslate_nhds with ⟨r, hrpos, hrsub⟩
  refine ⟨Q, hQ, r, hrpos, ?_⟩
  -- This ball is exactly the neighborhood on which the recentered graph stays in `Ω`.
  intro p hp
  exact hrsub hp

/-- Helper for Theorem I: any analytic open-set solution produces a recentered vector power series
at `0` with vanishing constant term. -/
private theorem recentered_solution_hasFPowerSeriesAt_zero {n : ℕ}
    {Ω : Set (ℂ × (Fin n → ℂ))} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ} {b : Fin n → ℂ}
    {U : Set ℂ} {χ : ℂ → Fin n → ℂ}
    (hχ : IsHolomorphicSystemSolutionOn Ω f 0 b U χ) :
    ∃ χSeries : PowerSeries (Fin n → ℂ),
      PowerSeries.constantCoeff χSeries = 0 ∧
      HasFPowerSeriesAt (fun z ↦ χ z - b)
        (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m χSeries) 0 := by
  -- Recenter the analytic solution by subtracting the initial value and choose its Taylor series.
  obtain ⟨P, hP⟩ := ((hχ.analytic 0 hχ.mem).sub analyticAt_const)
  let χSeries : PowerSeries (Fin n → ℂ) := PowerSeries.mk fun m ↦ P.coeff m
  have hχSeries :
      HasFPowerSeriesAt (fun z ↦ χ z - b)
        (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m χSeries) 0 := by
    -- Replace the arbitrary one-variable multilinear series by its coefficient packaging.
    have hpack :
        P = vectorOfScalarsSeries (fun m ↦ PowerSeries.coeff m χSeries) := by
      simpa [χSeries] using formalMultilinearSeries_eq_vectorOfScalarsSeries (P := P)
    exact hpack ▸ hP
  have hχSeries_zero_coeff : PowerSeries.coeff 0 χSeries = 0 := by
    -- The recentered function vanishes at `0`, so the constant coefficient is forced to be zero.
    have hP_zero : P.coeff 0 = 0 := by
      have hP_zero_eval : P 0 (fun _ ↦ (0 : ℂ)) = 0 := by
        simpa [hχ.initial] using hP.coeff_zero (fun _ ↦ (0 : ℂ))
      have hone : (1 : Fin 0 → ℂ) = fun _ ↦ (0 : ℂ) := by
        funext i
        exact Fin.elim0 i
      rw [FormalMultilinearSeries.coeff, hone, hP_zero_eval]
    simpa [χSeries] using hP_zero
  have hχSeries_zero : PowerSeries.constantCoeff χSeries = 0 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hχSeries_zero_coeff
  exact ⟨χSeries, hχSeries_zero, hχSeries⟩

/-- Helper for Theorem I: once the exact recentered formal vector solution is known, the remaining
source-faithful existence step is to realize that series as an actual holomorphic solution on a
smaller ball whose translated graph stays inside `Ω`. -/
private theorem sameOwner_eventuallyEq_at_zero {n : ℕ}
    {u v : ℂ → Fin n → ℂ} {P : FormalMultilinearSeries ℂ ℂ (Fin n → ℂ)}
    (hu : HasFPowerSeriesAt u P 0) (hv : HasFPowerSeriesAt v P 0) :
    u =ᶠ[𝓝 (0 : ℂ)] v := by
  -- Shrink both power-series witnesses to the same positive ball and then use uniqueness there.
  rcases hu with ⟨ru, huBall⟩
  rcases hv with ⟨rv, hvBall⟩
  have hrmin : 0 < min ru rv := lt_min huBall.r_pos hvBall.r_pos
  exact
    (huBall.mono hrmin inf_le_left).unique (hvBall.mono hrmin inf_le_right)
      |>.eventuallyEq_of_mem (Metric.eball_mem_nhds (0 : ℂ) hrmin)

/-- Helper for Theorem I: the formal derivative owner attached to the realized centered curve is
exactly the owner prescribed by the coefficient recursion. -/
private theorem recenteredFormalDerivativeOwner_eq {n : ℕ}
    {Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)}
    {φ : PowerSeries (Fin n → ℂ)}
    (hφ :
      PowerSeries.constantCoeff φ = 0 ∧
        ∀ m, PowerSeries.coeff (m + 1) φ =
          ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m) :
    ((ContinuousLinearMap.apply ℂ (Fin n → ℂ) (1 : ℂ)).compFormalMultilinearSeries
        (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m φ).derivSeries)
      =
      Q.comp (recenteredCurveSeries fun m ↦ PowerSeries.coeff m φ) := by
  -- Rewrite the derivative owner coefficientwise and cancel the scalar factor from the recursion.
  ext m i
  have hscaled :
      (m + 1 : ℂ) • PowerSeries.coeff (m + 1) φ =
        recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m := by
    calc
      (m + 1 : ℂ) • PowerSeries.coeff (m + 1) φ
          = (m + 1 : ℂ) •
              (((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m) := by
                rw [hφ.2 m]
      _ = (((m + 1 : ℂ) * (m + 1 : ℂ)⁻¹) •
            recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m) := by
              simp [smul_smul]
      _ = recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m := by
            have hmul : (m + 1 : ℂ) * (m + 1 : ℂ)⁻¹ = 1 := by
              field_simp [Nat.succ_ne_zero m]
            simp [hmul]
  -- The derivative-series coefficient is the scaled next Taylor coefficient.
  calc
    (((ContinuousLinearMap.apply ℂ (Fin n → ℂ) (1 : ℂ)).compFormalMultilinearSeries
        (vectorOfScalarsSeries fun k ↦ PowerSeries.coeff k φ).derivSeries).coeff m) i
        = ((m + 1 : ℂ) • PowerSeries.coeff (m + 1) φ) i := by
            rw [FormalMultilinearSeries.coeff,
              ContinuousLinearMap.compFormalMultilinearSeries_apply']
            change
              (((vectorOfScalarsSeries fun k ↦ PowerSeries.coeff k φ).derivSeries.coeff m) 1) i =
                _
            rw [FormalMultilinearSeries.derivSeries_coeff_one, vectorOfScalarsSeries_coeff]
            simp
    _ = (recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m) i := by
          simpa using congrArg (fun v : Fin n → ℂ ↦ v i) hscaled
    _ = (Q.comp (recenteredCurveSeries fun k ↦ PowerSeries.coeff k φ)).coeff m i := by
          rfl

/-- Helper for Theorem I: a centered analytic curve with vanishing value at `0` stays in any
prescribed small product ball after shrinking the source ball. -/
private theorem recenteredSeries_mapsTo_ball {n : ℕ}
    {η : ℂ → Fin n → ℂ} {P : FormalMultilinearSeries ℂ ℂ (Fin n → ℂ)} {R : ENNReal}
    (hη : HasFPowerSeriesOnBall η P 0 R) (hη0 : η 0 = 0) {r : ℝ} (hr : 0 < r) :
    ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧
      MapsTo (fun z : ℂ ↦ (z, η z)) (Metric.ball 0 r') (Metric.ball (0 : ℂ × (Fin n → ℂ)) r) := by
  -- Use continuity at the center to force the second coordinate into the same small target ball.
  have hηcont : ContinuousAt η 0 := by
    refine hη.continuousOn.continuousAt ?_
    exact Metric.eball_mem_nhds (0 : ℂ) hη.r_pos
  have hpre : (fun z : ℂ ↦ η z) ⁻¹' Metric.ball (0 : Fin n → ℂ) (r / 2) ∈ 𝓝 (0 : ℂ) := by
    have hrhalf : 0 < r / 2 := by linarith
    have hball : Metric.ball (0 : Fin n → ℂ) (r / 2) ∈ 𝓝 (η 0) := by
      simpa [hη0] using Metric.ball_mem_nhds (0 : Fin n → ℂ) hrhalf
    exact hηcont.preimage_mem_nhds hball
  rcases Metric.mem_nhds_iff.mp hpre with ⟨δ, hδpos, hδsub⟩
  refine ⟨min δ (r / 2), by positivity, ?_, ?_⟩
  · exact le_trans (min_le_right _ _) (by linarith)
  intro z hz
  have hzδ : z ∈ Metric.ball (0 : ℂ) δ := by
    exact Metric.mem_ball'.2 <| lt_of_lt_of_le (Metric.mem_ball'.1 hz) (min_le_left _ _)
  have hzsmall : z ∈ Metric.ball (0 : ℂ) (r / 2) := by
    exact Metric.mem_ball'.2 <| lt_of_lt_of_le (Metric.mem_ball'.1 hz) (min_le_right _ _)
  have hηsmall : η z ∈ Metric.ball (0 : Fin n → ℂ) (r / 2) := hδsub hzδ
  have hzNorm : ‖z‖ < r := by
    have : ‖z‖ < r / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzsmall
    linarith
  have hηNorm : ‖η z‖ < r := by
    have : ‖η z‖ < r / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hηsmall
    linarith
  simp [Metric.mem_ball, dist_eq_norm, hzNorm, hηNorm]

/-- Helper for Theorem I: any summable scalar coefficient majorant gives positive radius to the
coordinatewise packaged vector owner. -/
private theorem vectorOfScalarsSeries_radiusPos_of_summableScalarMajorant {n : ℕ}
    {a : ℕ → Fin n → ℂ} {A : ℕ → ℝ} {r : NNReal}
    (hr : 0 < r) (hsumA : Summable (fun m ↦ A m * (r : ℝ) ^ m))
    (hA : ∀ m i, ‖a m i‖ ≤ A m) :
    0 < (vectorOfScalarsSeries a).radius := by
  -- Prove the same radius lower bound for each scalar coordinate owner separately.
  have hcoord :
      ∀ i : Fin n,
        ((r : ENNReal) ≤ (FormalMultilinearSeries.ofScalars ℂ (fun m ↦ a m i)).radius) := by
    intro i
    apply FormalMultilinearSeries.le_radius_of_summable_norm
    refine Summable.of_nonneg_of_le ?_ ?_ hsumA
    · intro m
      positivity
    · intro m
      rw [FormalMultilinearSeries.ofScalars_norm]
      exact mul_le_mul_of_nonneg_right (hA m i) (pow_nonneg (by exact_mod_cast r.2) _)
  -- Then assemble the coordinatewise radius bounds using the finite-product `pi` owner API.
  have hradius :
      (r : ENNReal) ≤ (vectorOfScalarsSeries a).radius := by
    simpa [vectorOfScalarsSeries] using
      (FormalMultilinearSeries.le_radius_pi (p := fun i : Fin n ↦
        FormalMultilinearSeries.ofScalars ℂ (fun m ↦ a m i)) hcoord)
  exact lt_of_lt_of_le (by simpa [ENNReal.coe_pos] using hr) hradius

/-- Helper for Theorem I: the coordinatewise packaged vector owner has exactly the norm of its
vector coefficient at each degree. -/
private theorem vectorOfScalarsSeries_norm {n : ℕ} (a : ℕ → Fin n → ℂ) (m : ℕ) :
    ‖(vectorOfScalarsSeries a) m‖ = ‖a m‖ := by
  -- The `pi` owner takes the maximum of the coordinatewise scalar owner norms.
  change
    ‖ContinuousMultilinearMap.pi
        (fun i : Fin n ↦ (FormalMultilinearSeries.ofScalars ℂ (fun k ↦ a k i)) m)‖ = ‖a m‖
  rw [ContinuousMultilinearMap.opNorm_pi, Pi.norm_def, Pi.norm_def]
  congr
  ext i
  change ‖FormalMultilinearSeries.ofScalars ℂ (fun k ↦ a k i) m‖ = ‖a m i‖
  rw [FormalMultilinearSeries.ofScalars_norm]

/-- Helper for Theorem I: the recentered curve owner combines the fixed `X` coefficient and the
vector coefficient by the product norm. -/
private theorem recenteredCurveSeries_norm {n : ℕ} (a : ℕ → Fin n → ℂ) (m : ℕ) :
    ‖(recenteredCurveSeries a) m‖ = max ‖recenteredXCoeff m‖ ‖a m‖ := by
  -- The first component is the scalar `X` owner and the second component is the vector owner.
  change
    ‖((FormalMultilinearSeries.ofScalars ℂ recenteredXCoeff) m).prod
        ((vectorOfScalarsSeries a) m)‖ =
      max ‖recenteredXCoeff m‖ ‖a m‖
  rw [ContinuousMultilinearMap.opNorm_prod,
    FormalMultilinearSeries.ofScalars_norm, vectorOfScalarsSeries_norm]

/-- Helper for Theorem I: a weighted coefficient bound on `a` propagates to the full recentered
curve owner fed into the composition `Q.comp (recenteredCurveSeries a)`. -/
private theorem recenteredCurveSeries_weightedCoeffBudget {n : ℕ}
    {a : ℕ → Fin n → ℂ} {ρ D : NNReal}
    (hρD : (ρ : ℝ) ≤ D)
    (ha : ∀ m, ‖a m‖ * (ρ : ℝ) ^ m ≤ D) :
    ∀ m, ‖recenteredCurveSeries a m‖ * (ρ : ℝ) ^ m ≤ D := by
  intro m
  -- Rewrite the recentered owner norm into the max of the fixed `X` coefficient and the vector
  -- coefficient, then bound those two pieces separately.
  rw [recenteredCurveSeries_norm]
  rw [max_mul_of_nonneg _ _ (pow_nonneg (by exact_mod_cast ρ.2) _)]
  refine (max_le_iff.2 ?_)
  constructor
  · -- The `X` component contributes only in degree `1`, so it is controlled by `ρ ≤ D`.
    cases m with
    | zero =>
        simp [recenteredXCoeff]
    | succ m =>
        cases m with
        | zero =>
            simpa [recenteredXCoeff] using hρD
        | succ m =>
            simp [recenteredXCoeff]
  · -- The vector component is exactly the hypothesis on `a`.
    exact ha m

/-- Helper for Theorem I: the canonical formal solution is the unique series satisfying the exact
recentered multilinear coefficient recursion. -/
private theorem formalRecenteredSeries_eq_canonical {n : ℕ}
    {Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)}
    {φ : PowerSeries (Fin n → ℂ)}
    (hφ :
      PowerSeries.constantCoeff φ = 0 ∧
        ∀ m, PowerSeries.coeff (m + 1) φ =
          ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m) :
    φ = formalRecenteredVectorSolutionSeries Q := by
  -- Rewrite the user-facing series to the canonical recursively stabilized owner before tackling
  -- any radius argument.
  rcases existsUnique_formal_series_solution_for_recentered_multilinear_system Q with
    ⟨ξ, hξ, hξuniq⟩
  have hcanonical : formalRecenteredVectorSolutionSeries Q = ξ := by
    exact hξuniq _ (formalRecenteredVectorSolutionSeries_isSolution (Q := Q))
  exact (hξuniq _ hφ).trans hcanonical.symm

/-- Helper for Theorem I: package the vector coefficient norms as a scalar majorant series. -/
private noncomputable def scalarNormSeries {n : ℕ} (a : ℕ → Fin n → ℂ) : ℝ⟦X⟧ :=
  PowerSeries.mk fun m ↦ ‖a m‖

/-- Helper for Theorem I: package the operator norms of the outer multilinear owner as a scalar
power series. -/
private noncomputable def formalMultilinearSeriesNormSeries {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) : ℝ⟦X⟧ :=
  PowerSeries.mk fun m ↦ ‖Q m‖

/-- Helper for Theorem I: every coefficient of the scalar majorant `X + ∑ ‖aₘ‖ X^m` is
nonnegative. -/
private theorem scalarMajorantSeries_coeff_nonneg {n : ℕ} (a : ℕ → Fin n → ℂ) (m : ℕ) :
    0 ≤ PowerSeries.coeff m ((X : ℝ⟦X⟧) + scalarNormSeries a) := by
  cases m with
  | zero =>
      simp [scalarNormSeries]
  | succ m =>
      cases m with
      | zero =>
          have h : 0 ≤ (1 : ℝ) + ‖a 1‖ := by positivity
          simpa [PowerSeries.coeff_X, scalarNormSeries] using h
      | succ m =>
          simp [PowerSeries.coeff_X, scalarNormSeries]

/-- Helper for Theorem I: the recentered curve coefficient at degree `m` is bounded by the
corresponding coefficient of the scalar majorant `X + ∑ ‖aₘ‖ X^m`. -/
private theorem recenteredCurveSeries_norm_le_scalarMajorantCoeff {n : ℕ}
    {a : ℕ → Fin n → ℂ} (ha0 : a 0 = 0) (m : ℕ) :
    ‖recenteredCurveSeries a m‖ ≤
      PowerSeries.coeff m ((X : ℝ⟦X⟧) + scalarNormSeries a) := by
  cases m with
  | zero =>
      rw [recenteredCurveSeries_norm]
      simp [recenteredXCoeff, scalarNormSeries, ha0]
  | succ m =>
      cases m with
      | zero =>
          rw [recenteredCurveSeries_norm]
          refine (max_le_iff.2 ?_)
          constructor
          · simp [recenteredXCoeff, scalarNormSeries]
          · simp [scalarNormSeries]
      | succ m =>
          rw [recenteredCurveSeries_norm]
          have h : max ‖recenteredXCoeff (m + 2)‖ ‖a (m + 2)‖ ≤ ‖a (m + 2)‖ := by
            simp [recenteredXCoeff]
          have hnonneg : 0 ≤ PowerSeries.coeff (m + 2) (X : ℝ⟦X⟧) := by
            simp [PowerSeries.coeff_X]
          exact le_trans h <| by
            simp [PowerSeries.coeff_X, scalarNormSeries]

/-- Helper for Theorem I: the norm of each recentered composition coefficient is dominated by the
matching coefficient of the scalar substitution built from the outer operator norms and the inner
scalar majorant `X + ∑ ‖aₘ‖ X^m`. -/
private theorem recenteredComposedCoeff_norm_le_scalarSubstCoeff {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ))
    {a : ℕ → Fin n → ℂ} (ha0 : a 0 = 0) (m : ℕ) :
    ‖recenteredComposedCoeff Q a m‖ ≤
      PowerSeries.coeff m
        ((formalMultilinearSeriesNormSeries Q).subst
          ((X : ℝ⟦X⟧) + scalarNormSeries a)) := by
  let U : ℝ⟦X⟧ := (X : ℝ⟦X⟧) + scalarNormSeries a
  have hU0 : PowerSeries.constantCoeff U = 0 := by
    simp [U, scalarNormSeries, ha0]
  calc
    ‖recenteredComposedCoeff Q a m‖
        = ‖∑ c : Composition m,
            Q c.length (fun i ↦ (recenteredCurveSeries a).coeff (c.blocksFun i))‖ := by
              rw [recenteredComposedCoeff, FormalMultilinearSeries.coeff,
                FormalMultilinearSeries.comp, ContinuousMultilinearMap.sum_apply]
              refine congrArg norm ?_
              refine Finset.sum_congr rfl ?_
              intro c hc
              simp only [FormalMultilinearSeries.compAlongComposition_apply]
              refine congrArg (Q c.length) ?_
              funext i
              simp [FormalMultilinearSeries.applyComposition]
    _ ≤ ∑ c : Composition m,
          ‖Q c.length (fun i ↦ (recenteredCurveSeries a).coeff (c.blocksFun i))‖ := by
            exact norm_sum_le _ _
    _ ≤ ∑ c : Composition m,
          ‖Q c.length‖ * ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) U := by
            refine Finset.sum_le_sum ?_
            intro c hc
            calc
              ‖Q c.length (fun i ↦ (recenteredCurveSeries a).coeff (c.blocksFun i))‖
                  ≤ ‖Q c.length‖ * ∏ i : Fin c.length,
                      ‖(recenteredCurveSeries a).coeff (c.blocksFun i)‖ := by
                        exact ContinuousMultilinearMap.le_opNorm (Q c.length) _
              _ ≤ ‖Q c.length‖ * ∏ i : Fin c.length,
                    PowerSeries.coeff (c.blocksFun i) U := by
                      gcongr with i
                      simpa [FormalMultilinearSeries.norm_apply_eq_norm_coef] using
                        recenteredCurveSeries_norm_le_scalarMajorantCoeff (a := a) ha0
                          (c.blocksFun i)
    _ =
        ((FormalMultilinearSeries.ofScalars ℝ
            (fun k ↦ ‖Q k‖)).comp
          (FormalMultilinearSeries.ofScalars ℝ (fun k ↦ PowerSeries.coeff k U))).coeff m := by
            symm
            simpa [formalMultilinearSeriesNormSeries] using
              ofScalars_comp_coeff_eq_sum_compositions
                (formalMultilinearSeriesNormSeries Q) U m
    _ = PowerSeries.coeff m ((formalMultilinearSeriesNormSeries Q).subst U) := by
          simpa [formalMultilinearSeriesNormSeries] using
            (scalar_subst_coeff_eq_ofScalars_comp_coeff
              (formalMultilinearSeriesNormSeries Q) U hU0 m).symm

/-- Helper for Theorem I: the exact centered formal solution has positive convergence radius once
its coefficient recursion is controlled by the analytic recentered owner. -/
private theorem formalRecenteredVectorSolutionSeries_norm_le_scalarFixedPoint {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ))
    {Φ : ℝ⟦X⟧} (hΦ0 : PowerSeries.constantCoeff Φ = 0)
    (hΦrec : ∀ m, PowerSeries.coeff (m + 1) Φ =
      ((m + 1 : ℝ)⁻¹) * PowerSeries.coeff m
        ((formalMultilinearSeriesNormSeries Q).subst ((X : ℝ⟦X⟧) + Φ)))
    (hΦnonneg : ∀ m, 0 ≤ PowerSeries.coeff m Φ) :
    ∀ m,
      ‖PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Q)‖ ≤
        PowerSeries.coeff m Φ := by
  let ξ : PowerSeries (Fin n → ℂ) := formalRecenteredVectorSolutionSeries Q
  let S : ℝ⟦X⟧ := formalMultilinearSeriesNormSeries Q
  rcases formalRecenteredVectorSolutionSeries_isSolution Q with ⟨hξ0, hξrec⟩
  have hSnonneg : ∀ d, 0 ≤ PowerSeries.coeff d S := by
    -- The scalar owner coefficients are operator norms, hence nonnegative.
    intro d
    simp [S, formalMultilinearSeriesNormSeries]
  have hξnorm :
      ∀ M, ∀ k ≤ M, ‖PowerSeries.coeff k ξ‖ ≤ PowerSeries.coeff k Φ := by
    intro M
    induction M with
    | zero =>
        intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst hk0
        -- Both the vector solution and the scalar fixed point start with vanishing constant term.
        simp [ξ, PowerSeries.coeff_zero_eq_constantCoeff_apply, hξ0, hΦ0]
    | succ M ih =>
        intro k hk
        by_cases hkM : k ≤ M
        · exact ih k hkM
        · have hk_eq : k = M + 1 := by omega
          subst hk_eq
          have ha0 : (fun k ↦ PowerSeries.coeff k ξ) 0 = 0 := by
            simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hξ0
          let U : ℝ⟦X⟧ := (X : ℝ⟦X⟧) + scalarNormSeries (fun k ↦ PowerSeries.coeff k ξ)
          let V : ℝ⟦X⟧ := (X : ℝ⟦X⟧) + Φ
          have hU0 : PowerSeries.constantCoeff U = 0 := by
            simp [U, scalarNormSeries, ha0]
          have hV0 : PowerSeries.constantCoeff V = 0 := by
            simp [V, hΦ0]
          have hU_nonneg : ∀ j ≤ M, 0 ≤ PowerSeries.coeff j U := by
            -- The norm majorant series has nonnegative coefficients in every degree.
            intro j hj
            simpa [U] using scalarMajorantSeries_coeff_nonneg (a := fun k ↦ PowerSeries.coeff k ξ) j
          have hV_nonneg : ∀ j ≤ M, 0 ≤ PowerSeries.coeff j V := by
            -- The scalar fixed point already has nonnegative coefficients, so adding `X`
            -- preserves nonnegativity.
            intro j hj
            cases j with
            | zero =>
                simp [V, hΦ0]
            | succ j =>
                cases j with
                | zero =>
                    have hΦ1 : 0 ≤ PowerSeries.coeff 1 Φ := hΦnonneg 1
                    simpa [V] using add_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hΦ1
                | succ j =>
                    simpa [V, PowerSeries.coeff_X] using hΦnonneg (j + 2)
          have hU_le_V : ∀ j ≤ M, PowerSeries.coeff j U ≤ PowerSeries.coeff j V := by
            -- The induction hypothesis controls the vector coefficient norms through degree `M`.
            intro j hj
            cases j with
            | zero =>
                simp [U, V, scalarNormSeries, ha0, hΦ0]
            | succ j =>
                cases j with
                | zero =>
                    have hstep : ‖PowerSeries.coeff 1 ξ‖ ≤ PowerSeries.coeff 1 Φ := ih 1 hj
                    simpa [U, V, scalarNormSeries] using add_le_add_left hstep 1
                | succ j =>
                    have hj' : j + 2 ≤ M := by omega
                    simpa [U, V, scalarNormSeries, PowerSeries.coeff_X] using ih (j + 2) hj'
          have hsubst_le :
              PowerSeries.coeff M (S.subst U) ≤ PowerSeries.coeff M (S.subst V) := by
            -- The scalar substitution bridge is the only interface step between the vector
            -- recursion and the scalar fixed point recursion.
            exact coeffSubst_mono_of_nonnegative_prefixMajorant hSnonneg hU0 hV0
              hU_nonneg hV_nonneg hU_le_V
          have hnormRec :
              ‖PowerSeries.coeff (M + 1) ξ‖ =
                ((M + 1 : ℝ)⁻¹) *
                  ‖recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k ξ) M‖ := by
            have hInvNorm : ‖((M + 1 : ℂ)⁻¹)‖ = ((M + 1 : ℝ)⁻¹) := by
              have hNatNormAbs : ‖(M + 1 : ℂ)‖ = |(M + 1 : ℝ)| := by
                simpa using (Complex.norm_real (M + 1 : ℝ))
              have hNatNonneg : 0 ≤ (M + 1 : ℝ) := by
                positivity
              rw [norm_inv]
              congr 1
              rw [hNatNormAbs]
              rw [abs_of_nonneg hNatNonneg]
            -- Rewrite the vector recursion and compute the norm of the real scalar factor.
            calc
              ‖PowerSeries.coeff (M + 1) ξ‖
                  = ‖((M + 1 : ℂ)⁻¹) •
                      recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k ξ) M‖ := by
                        rw [hξrec M]
              _ = ‖((M + 1 : ℂ)⁻¹)‖ *
                    ‖recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k ξ) M‖ := by
                      rw [norm_smul]
              _ = ((M + 1 : ℝ)⁻¹) *
                    ‖recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k ξ) M‖ := by
                      rw [hInvNorm]
          -- Compare the vector recursion coefficient with the scalar fixed point recursion.
          calc
            ‖PowerSeries.coeff (M + 1) ξ‖
                = ((M + 1 : ℝ)⁻¹) *
                    ‖recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k ξ) M‖ := hnormRec
            _ ≤ ((M + 1 : ℝ)⁻¹) * PowerSeries.coeff M (S.subst U) := by
                  gcongr
                  simpa [S, U] using
                    recenteredComposedCoeff_norm_le_scalarSubstCoeff Q ha0 M
            _ ≤ ((M + 1 : ℝ)⁻¹) * PowerSeries.coeff M (S.subst V) := by
                  exact mul_le_mul_of_nonneg_left hsubst_le (by positivity)
            _ = PowerSeries.coeff (M + 1) Φ := by
                  simpa [S, V] using (hΦrec M).symm
  exact fun m ↦ hξnorm m m le_rfl

/-- Helper for Theorem I: the exact centered formal solution has positive convergence radius once
its coefficient recursion is controlled by the analytic recentered owner. -/
private theorem formalRecenteredVectorSeries_radiusPos {n : ℕ}
    {f : ℂ → (Fin n → ℂ) → Fin n → ℂ} {b : Fin n → ℂ}
    {Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)}
    (hQ : HasFPowerSeriesAt (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 (b + p.2)) Q (0, 0))
    {φ : PowerSeries (Fin n → ℂ)}
    (hφ :
      PowerSeries.constantCoeff φ = 0 ∧
        ∀ m, PowerSeries.coeff (m + 1) φ =
          ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m) :
    0 < (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m φ).radius := by
  -- Route correction: the old uniform weighted-coefficient ball was false for arbitrary composed
  -- owners. The correct frontier is the scalar weighted-summability majorant from Proposition 5.1.
  rw [formalRecenteredSeries_eq_canonical (Q := Q) hφ]
  let S : ℝ⟦X⟧ := formalMultilinearSeriesNormSeries Q
  have hSrad : 0 < S.radius := by
    -- The scalar norm owner inherits a positive radius from the analytic multilinear germ `Q`.
    rcases ENNReal.lt_iff_exists_nnreal_btwn.mp (HasFPowerSeriesAt.radius_pos hQ) with
      ⟨r, hrpos, hrQ⟩
    have hradius :
        (r : ENNReal) ≤ S.radius := by
      change
        (r : ENNReal) ≤
          (FormalMultilinearSeries.ofScalars ℝ
            (fun m ↦ PowerSeries.coeff m (formalMultilinearSeriesNormSeries Q))).radius
      apply FormalMultilinearSeries.le_radius_of_summable_norm
      simpa [S, formalMultilinearSeriesNormSeries, FormalMultilinearSeries.ofScalars_norm] using
        Q.summable_norm_mul_pow hrQ
    exact lt_of_lt_of_le (by simpa [ENNReal.coe_pos] using hrpos) hradius
  obtain ⟨Φ, hΦ0, hΦrec⟩ := existsScalarSubstFormalSolution S
  have hS0 : 0 ≤ PowerSeries.constantCoeff S := by
    -- The constant coefficient of the scalar norm series is a norm.
    simp [S, formalMultilinearSeriesNormSeries]
  have hSnonneg : ∀ d, 0 ≤ PowerSeries.coeff d S := by
    -- Every scalar coefficient of the norm owner is a norm.
    intro d
    simp [S, formalMultilinearSeriesNormSeries]
  have hΦnonneg : ∀ m, 0 ≤ PowerSeries.coeff m Φ :=
    scalarSubstFormalSolution_coeff_nonneg hSnonneg hΦ0 hΦrec
  have hΦrad : 0 < Φ.radius :=
    scalarSubstFormalSolution_radiusPos hS0 hSrad hΦ0 hΦrec
  have hmajorant :
      ∀ m, ‖PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Q)‖ ≤ PowerSeries.coeff m Φ :=
    formalRecenteredVectorSolutionSeries_norm_le_scalarFixedPoint (Q := Q) hΦ0 hΦrec hΦnonneg
  rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hΦrad with ⟨r, hr0, hrΦ⟩
  have hr0' : 0 < r := by
    simpa [NNReal.coe_pos] using hr0
  have hsumΦ :
      Summable (fun m : ℕ ↦ PowerSeries.coeff m Φ * (r : ℝ) ^ m) := by
    -- Inside the positive radius of `Φ`, the weighted coefficients are summable; coefficientwise
    -- nonnegativity removes the absolute values.
    simpa [Real.norm_eq_abs, abs_of_nonneg, hΦnonneg] using
      (summable_norm_coeff_mul_pow_of_lt_radius Φ hrΦ)
  -- Feed the scalar majorant into the existing vector-radius bridge.
  refine vectorOfScalarsSeries_radiusPos_of_summableScalarMajorant
    (a := fun m ↦ PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Q))
    (A := fun m ↦ PowerSeries.coeff m Φ) hr0' hsumΦ ?_
  intro m i
  have hcoord :
      ‖PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Q) i‖ ≤
        ‖PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Q)‖ := by
    -- Coordinate norms are bounded by the finite supremum norm on `Fin n → ℂ`.
    rw [Pi.norm_def]
    exact_mod_cast
      (Finset.le_sup
        (s := Finset.univ)
        (f := fun j : Fin n ↦ ‖PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Q) j‖₊)
        (Finset.mem_univ i))
  exact le_trans hcoord (hmajorant m)

/-- Helper for Theorem I: once the exact recentered formal vector solution is known, the remaining
source-faithful existence step is to realize that series as an actual holomorphic solution on a
smaller ball whose translated graph stays inside `Ω`. -/
private theorem solutionOn_of_recentered_formal_series_on_ball {n : ℕ}
    {Ω : Set (ℂ × (Fin n → ℂ))} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ} {b : Fin n → ℂ}
    {Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)}
    (hQ : HasFPowerSeriesAt (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 (b + p.2)) Q (0, 0))
    {r : ℝ} (hrpos : 0 < r)
    (hballΩ : MapsTo (fun p : ℂ × (Fin n → ℂ) ↦ (p.1, b + p.2))
      (Metric.ball (0 : ℂ × (Fin n → ℂ)) r) Ω)
    {φ : PowerSeries (Fin n → ℂ)}
    (hφ :
      PowerSeries.constantCoeff φ = 0 ∧
        ∀ m, PowerSeries.coeff (m + 1) φ =
          ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m) :
    ∃ U : Set ℂ, ∃ ψ : ℂ → Fin n → ℂ,
      IsHolomorphicSystemSolutionOn Ω f 0 b U ψ ∧
      HasFPowerSeriesAt (fun z ↦ ψ z - b)
        (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m φ) 0 := by
  -- Route correction: the remaining existence gap is not the formal recursion anymore; it is the
  -- analytic realization of that exact recentered formal series on a small ball.
  let P : FormalMultilinearSeries ℂ ℂ (Fin n → ℂ) :=
    vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m φ
  let η : ℂ → Fin n → ℂ := P.sum
  have hPradius : 0 < P.radius := by
    -- This is the single remaining radius blocker for the existence construction.
    simpa [P] using formalRecenteredVectorSeries_radiusPos (b := b) (Q := Q) hQ hφ
  have hηball : HasFPowerSeriesOnBall η P 0 P.radius := by
    simpa [η, P] using P.hasFPowerSeriesOnBall hPradius
  have hηzero : η 0 = 0 := by
    -- The formal solution has zero constant term, so its realized sum also vanishes at the center.
    have hcoeff0 : PowerSeries.coeff 0 φ = η 0 := by
      simpa [η, P, vectorOfScalarsSeries_coeff] using
        hηball.coeff_zero (fun _ ↦ (0 : ℂ))
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply, hφ.1] using hcoeff0.symm
  have hPderivOwner :
      ((ContinuousLinearMap.apply ℂ (Fin n → ℂ) (1 : ℂ)).compFormalMultilinearSeries P.derivSeries)
        =
        Q.comp (recenteredCurveSeries fun m ↦ PowerSeries.coeff m φ) := by
    -- This is the exact formal differential equation encoded as equality of owners.
    simpa [P] using recenteredFormalDerivativeOwner_eq (Q := Q) hφ
  rcases hQ with ⟨RQ, hQball⟩
  rcases ENNReal.lt_iff_exists_real_btwn.mp hQball.r_pos with ⟨ρQ, hρQ_nonneg, hρQ_pos, hρQ_lt⟩
  have hρQ_pos_real : 0 < ρQ := by
    simpa [ENNReal.ofReal_pos] using hρQ_pos
  rcases ENNReal.lt_iff_exists_real_btwn.mp hPradius with ⟨ρP, hρP_nonneg, hρP_pos, hρP_lt⟩
  have hρP_pos_real : 0 < ρP := by
    simpa [ENNReal.ofReal_pos] using hρP_pos
  let ρ : ℝ := min r (min ρQ ρP)
  have hρpos : 0 < ρ := by
    exact lt_min hrpos (lt_min hρQ_pos_real hρP_pos_real)
  have hρleQ : ENNReal.ofReal ρ ≤ RQ := by
    have hρleρQ : ρ ≤ ρQ := by
      exact le_trans (min_le_right r (min ρQ ρP)) (min_le_left ρQ ρP)
    exact le_trans (ENNReal.ofReal_le_ofReal hρleρQ) (le_of_lt hρQ_lt)
  have hρleP : ENNReal.ofReal ρ ≤ P.radius := by
    have hρleρP : ρ ≤ ρP := by
      exact le_trans (min_le_right r (min ρQ ρP)) (min_le_right ρQ ρP)
    exact le_trans (ENNReal.ofReal_le_ofReal hρleρP) (le_of_lt hρP_lt)
  have hηsmall : HasFPowerSeriesOnBall η P 0 (ENNReal.ofReal ρ) :=
    hηball.mono (by simpa using hρpos) hρleP
  have hQsmall :
      HasFPowerSeriesOnBall
        (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 (b + p.2))
        Q
        (0, 0)
        (ENNReal.ofReal ρ) :=
    hQball.mono (by simpa using hρpos) hρleQ
  rcases recenteredSeries_mapsTo_ball (hη := hηsmall) hηzero (r := ρ) hρpos with
    ⟨ρ', hρ'pos, hρ'leρ, hcurveBall⟩
  have hUsubρ : Metric.ball (0 : ℂ) ρ' ⊆ Metric.ball 0 ρ := by
    intro z hz
    exact Metric.mem_ball'.2 <| lt_of_lt_of_le (Metric.mem_ball'.1 hz) hρ'leρ
  have hcurveToΩ : MapsTo (fun z : ℂ ↦ (z, b + η z)) (Metric.ball 0 ρ') Ω := by
    intro z hz
    have hzBall : (z, η z) ∈ Metric.ball (0 : ℂ × (Fin n → ℂ)) r := by
      have hzρ : (z, η z) ∈ Metric.ball (0 : ℂ × (Fin n → ℂ)) ρ := hcurveBall hz
      exact Metric.mem_ball'.2 <| lt_of_lt_of_le (Metric.mem_ball'.1 hzρ) (min_le_left _ _)
    simpa [η] using hballΩ hzBall
  have hηanalytic : AnalyticOnNhd ℂ η (Metric.ball 0 ρ') := by
    have hηanalyticρ : AnalyticOnNhd ℂ η (Metric.ball 0 ρ) := by
      simpa [η, Metric.eball_ofReal] using hηsmall.analyticOnNhd
    exact hηanalyticρ.mono hUsubρ
  let ψ : ℂ → Fin n → ℂ := fun z ↦ b + η z
  have hψanalytic : AnalyticOnNhd ℂ ψ (Metric.ball 0 ρ') := by
    -- Add the initial value back after realizing the centered analytic series.
    simpa [ψ] using analyticOnNhd_const.add hηanalytic
  have hcurveAnalytic :
      AnalyticOnNhd ℂ (fun z : ℂ ↦ (z, η z)) (Metric.ball 0 ρ') :=
    analyticOnNhd_id.prod hηanalytic
  have hQanalytic :
      AnalyticOnNhd ℂ (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 (b + p.2))
        (Metric.ball (0 : ℂ × (Fin n → ℂ)) ρ) := by
    simpa [Metric.eball_ofReal] using hQsmall.analyticOnNhd
  have hRhsAnalytic : AnalyticOnNhd ℂ (fun z : ℂ ↦ f z (ψ z)) (Metric.ball 0 ρ') := by
    -- The recentered right-hand side is analytic on the product ball, so composing with the
    -- realized centered curve gives an analytic right-hand side on the source ball.
    simpa [ψ] using hQanalytic.comp hcurveAnalytic (fun z hz ↦ hcurveBall hz)
  have hηcurveAt :
      HasFPowerSeriesAt (fun z : ℂ ↦ (z, η z))
        (recenteredCurveSeries fun m ↦ PowerSeries.coeff m φ)
        0 := by
    -- The realized centered curve has the canonical recentered owner at the origin.
    simpa [P] using recenteredCurve_hasFPowerSeriesAt (u := η) (a := fun m ↦ PowerSeries.coeff m φ)
      hηsmall.hasFPowerSeriesAt
  have hηderivAt :
      HasFPowerSeriesAt (deriv η)
        ((ContinuousLinearMap.apply ℂ (Fin n → ℂ) (1 : ℂ)).compFormalMultilinearSeries
          P.derivSeries)
        0 := by
    -- Differentiate the realized centered series once and evaluate the one-dimensional derivative.
    simpa [η] using
      ((ContinuousLinearMap.apply ℂ (Fin n → ℂ) (1 : ℂ)).comp_hasFPowerSeriesOnBall
        hηsmall.fderiv).hasFPowerSeriesAt
  have hRhsAt :
      HasFPowerSeriesAt (fun z : ℂ ↦ f z (ψ z))
        (Q.comp (recenteredCurveSeries fun m ↦ PowerSeries.coeff m φ))
        0 := by
    -- Compose the recentered right-hand side owner with the realized centered curve owner at `0`.
    have hQzero :
        HasFPowerSeriesAt (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 (b + p.2))
          Q
          ((fun z : ℂ ↦ (z, η z)) 0) := by
      simpa [hηzero] using hQball.hasFPowerSeriesAt
    simpa [Function.comp, ψ] using
      (HasFPowerSeriesAt.comp
        (g := fun p : ℂ × (Fin n → ℂ) ↦ f p.1 (b + p.2))
        (f := fun z : ℂ ↦ (z, η z))
        hQzero
        hηcurveAt)
  have hEventually : deriv η =ᶠ[𝓝 (0 : ℂ)] fun z ↦ f z (ψ z) := by
    -- The derivative and the right-hand side share the same owner at the origin.
    refine sameOwner_eventuallyEq_at_zero ?_ hRhsAt
    simpa [hPderivOwner] using hηderivAt
  have hDerivEqOn :
      Set.EqOn (deriv ψ) (fun z ↦ f z (ψ z)) (Metric.ball 0 ρ') := by
    -- Propagate the local equality at `0` to the whole connected source ball by analyticity.
    have hψderivAnalytic : AnalyticOnNhd ℂ (deriv ψ) (Metric.ball 0 ρ') := by
      exact hψanalytic.deriv_of_isOpen Metric.isOpen_ball
    have h0mem : (0 : ℂ) ∈ Metric.ball 0 ρ' := by
      simpa [Metric.mem_ball, dist_eq_norm] using hρ'pos
    have hEventually' : deriv ψ =ᶠ[𝓝 (0 : ℂ)] fun z ↦ f z (ψ z) := by
      filter_upwards [hEventually] with z hz
      simpa [ψ] using hz
    exact hψderivAnalytic.eqOn_of_preconnected_of_eventuallyEq hRhsAnalytic
      Metric.isPreconnected_ball h0mem hEventually'
  refine ⟨Metric.ball 0 ρ', ψ, ?_, ?_⟩
  · refine ⟨Metric.isOpen_ball, ?_, hψanalytic, hcurveToΩ, ?_, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm] using hρ'pos
    · simp [ψ, hηzero]
    · intro z hz
      -- Analyticity of `ψ` supplies the derivative, and the analytic continuation step identifies
      -- that derivative with the given right-hand side on the whole working ball.
      simpa [hDerivEqOn hz] using (hψanalytic z hz).hasStrictDerivAt.hasDerivAt
  · -- Recenter the realized solution by subtracting `b`; this recovers the exact centered owner.
    simpa [ψ, η] using hηsmall.hasFPowerSeriesAt

/-- Helper for Theorem I: any analytic competitor has the same recentered Taylor data as the exact
formal solution, so its germ agrees with the realized solution germ. -/
private theorem germ_eq_of_recentered_formal_solution {n : ℕ}
    {Ω : Set (ℂ × (Fin n → ℂ))} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ} {b : Fin n → ℂ}
    {Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)}
    (hQ : HasFPowerSeriesAt (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 (b + p.2)) Q (0, 0))
    {φ : PowerSeries (Fin n → ℂ)}
    (hφ :
      PowerSeries.constantCoeff φ = 0 ∧
        ∀ m, PowerSeries.coeff (m + 1) φ =
          ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m)
    {ψ : ℂ → Fin n → ℂ}
    (hψseries : HasFPowerSeriesAt (fun z ↦ ψ z - b)
      (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m φ) 0) :
    ∀ {V : Set ℂ} {χ : ℂ → Fin n → ℂ}, IsHolomorphicSystemSolutionOn Ω f 0 b V χ →
      (χ : Germ (𝓝 (0 : ℂ)) (Fin n → ℂ)) = (ψ : Germ (𝓝 (0 : ℂ)) (Fin n → ℂ)) := by
  intro V χ hχ
  -- Route correction: uniqueness should proceed by recentering `χ`, showing its Taylor series
  -- satisfies the same exact multilinear recursion, and invoking formal uniqueness before passing
  -- back to germs.
  rcases recentered_solution_hasFPowerSeriesAt_zero (b := b) hχ with
    ⟨χSeries, hχSeries0, hχSeries⟩
  -- Compose the recentered RHS Taylor model with the centered competitor curve.
  have hQχ :
      HasFPowerSeriesAt (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 (b + p.2))
        Q
        ((fun z : ℂ ↦ (z, χ z - b)) 0) := by
    simpa [hχ.initial] using hQ
  have hχcurve :
      HasFPowerSeriesAt (fun z : ℂ ↦ (z, χ z - b))
        (recenteredCurveSeries fun m ↦ PowerSeries.coeff m χSeries)
        0 :=
    recenteredCurve_hasFPowerSeriesAt hχSeries
  have hχrhs :
      HasFPowerSeriesAt
        (fun z : ℂ ↦ f z (χ z))
        (Q.comp (recenteredCurveSeries fun m ↦ PowerSeries.coeff m χSeries))
        0 := by
    convert
      (HasFPowerSeriesAt.comp
        (g := fun p : ℂ × (Fin n → ℂ) ↦ f p.1 (b + p.2))
        (f := fun z : ℂ ↦ (z, χ z - b))
        hQχ
        hχcurve) using 1
    ext z
    simp
  have hχSeriesAt := hχSeries
  have hχSeriesOnBallAt := hχSeriesAt
  rcases hχSeriesOnBallAt with ⟨rχ, hχSeriesOnBall⟩
  have hχderivSeries :
      HasFPowerSeriesAt
        (deriv χ)
        ((ContinuousLinearMap.apply ℂ (Fin n → ℂ) (1 : ℂ)).compFormalMultilinearSeries
          (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m χSeries).derivSeries)
        0 := by
    convert
      ((ContinuousLinearMap.apply ℂ (Fin n → ℂ) (1 : ℂ)).comp_hasFPowerSeriesOnBall
        hχSeriesOnBall.fderiv).hasFPowerSeriesAt using 1
    ext z
    simp
  have hχderivEq :
      deriv χ =ᶠ[𝓝 (0 : ℂ)] fun z ↦ f z (χ z) := by
    filter_upwards [hχ.isOpen.mem_nhds hχ.mem] with z hz
    simpa using (hχ.deriv_eq hz).deriv
  have hχderivOwners :
      ((ContinuousLinearMap.apply ℂ (Fin n → ℂ) (1 : ℂ)).compFormalMultilinearSeries
          (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m χSeries).derivSeries)
        =
        Q.comp (recenteredCurveSeries fun m ↦ PowerSeries.coeff m χSeries) :=
    hχderivSeries.eq_formalMultilinearSeries_of_eventually hχrhs hχderivEq
  have hχrec :
      ∀ m, PowerSeries.coeff (m + 1) χSeries =
        ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k χSeries) m := by
    intro m
    have hcoeff :=
      congrArg
        (fun P : FormalMultilinearSeries ℂ ℂ (Fin n → ℂ) ↦ P.coeff m)
        hχderivOwners
    have hscaled :
        (m + 1 : ℂ) • PowerSeries.coeff (m + 1) χSeries =
          recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k χSeries) m := by
      calc
        (m + 1 : ℂ) • PowerSeries.coeff (m + 1) χSeries
            =
              (((ContinuousLinearMap.apply ℂ (Fin n → ℂ) (1 : ℂ)).compFormalMultilinearSeries
                  (vectorOfScalarsSeries fun k ↦ PowerSeries.coeff k χSeries).derivSeries).coeff
                m) := by
                  rw [FormalMultilinearSeries.coeff,
                    ContinuousLinearMap.compFormalMultilinearSeries_apply']
                  change
                    (m + 1 : ℂ) • PowerSeries.coeff (m + 1) χSeries =
                      ((vectorOfScalarsSeries fun k ↦ PowerSeries.coeff k χSeries).derivSeries.coeff
                        m) 1
                  rw [FormalMultilinearSeries.derivSeries_coeff_one]
                  rw [vectorOfScalarsSeries_coeff]
                  rw [← Nat.cast_smul_eq_nsmul ℂ]
                  simp
        _ = (Q.comp (recenteredCurveSeries fun k ↦ PowerSeries.coeff k χSeries)).coeff m := hcoeff
        _ = recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k χSeries) m := rfl
    have hinv :
        ((m + 1 : ℂ)⁻¹) * (m + 1 : ℂ) = 1 := by
      exact inv_mul_cancel₀ <| by exact_mod_cast Nat.succ_ne_zero m
    calc
      PowerSeries.coeff (m + 1) χSeries
          = (((m + 1 : ℂ)⁻¹) * (m + 1 : ℂ)) • PowerSeries.coeff (m + 1) χSeries := by
              simp [hinv]
      _ = ((m + 1 : ℂ)⁻¹) • ((m + 1 : ℂ) • PowerSeries.coeff (m + 1) χSeries) := by
            simp [smul_smul]
      _ = ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k χSeries) m := by
            rw [hscaled]
  have hχeq :
      χSeries = φ := by
    rcases existsUnique_formal_series_solution_for_recentered_multilinear_system Q with
      ⟨ξ, hξ, hξuniq⟩
    exact (hξuniq _ ⟨hχSeries0, hχrec⟩).trans (hξuniq _ hφ).symm
  have hχsame :
      HasFPowerSeriesAt (fun z ↦ χ z - b)
        (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m φ)
        0 := by
    simpa [hχeq] using hχSeriesAt
  rcases hχsame with ⟨rχ', hχsameOnBall⟩
  rcases hψseries with ⟨rψ, hψseriesOnBall⟩
  have hrmin : 0 < min rχ' rψ := lt_min hχsameOnBall.r_pos hψseriesOnBall.r_pos
  have hsubEq :
      (fun z ↦ χ z - b) =ᶠ[𝓝 (0 : ℂ)] fun z ↦ ψ z - b := by
    exact
      (hχsameOnBall.mono hrmin inf_le_left).unique
        (hψseriesOnBall.mono hrmin inf_le_right)
        |>.eventuallyEq_of_mem (Metric.eball_mem_nhds (0 : ℂ) hrmin)
  have hEq : χ =ᶠ[𝓝 (0 : ℂ)] ψ := by
    filter_upwards [hsubEq] with z hz
    simpa using hz
  exact Germ.coe_eq.mpr hEq

/-- Cartan section27 0001_Theorem_I (Theorem I): the holomorphic Cauchy problem for a first-order
system with initial value `b` at `0` has a unique local holomorphic solution germ. -/
theorem unique_local_solution_holomorphic_system {n : ℕ}
    {Ω : Set (ℂ × (Fin n → ℂ))} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ} {b : Fin n → ℂ}
    (hΩ : IsOpen Ω) (h0 : ((0 : ℂ), b) ∈ Ω)
    (hf : AnalyticOnNhd ℂ (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 p.2) Ω) :
    ∃! φ : Germ (𝓝 (0 : ℂ)) (Fin n → ℂ), IsHolomorphicSystemSolution Ω f 0 b φ := by
  -- Route correction: the old two-variable `R⟦X,Y⟧` bridge is not adequate for a coupled vector
  -- system. The verified prefix now uses the correct multilinear Taylor germ of the recentered RHS.
  rcases recentered_rhs_hasFPowerSeriesAt (b := b) hΩ h0 hf with ⟨Q, hQ, r, hrpos, hballΩ⟩
  rcases existsUnique_formal_series_solution_for_recentered_multilinear_system Q with
    ⟨φ, hφ, hφ_unique⟩
  rcases solutionOn_of_recentered_formal_series_on_ball
      (hQ := hQ) hrpos hballΩ hφ with ⟨U, ψ, hψ, hψseries⟩
  refine ⟨(ψ : Germ (𝓝 (0 : ℂ)) (Fin n → ℂ)), hψ.isHolomorphicSystemSolution, ?_⟩
  intro χ hχ
  -- The realized solution is unique because every analytic competitor has the same recentered
  -- Taylor data and hence the same germ at `0`.
  rcases hχ with ⟨V, χ', hχ', hχgerm⟩
  have hχeq :
      (χ' : Germ (𝓝 (0 : ℂ)) (Fin n → ℂ)) = (ψ : Germ (𝓝 (0 : ℂ)) (Fin n → ℂ)) :=
    germ_eq_of_recentered_formal_solution (hQ := hQ) (ψ := ψ) hφ hψseries hχ'
  exact hχgerm.symm.trans hχeq

/-- Neighborhood-representative bridge for Theorem I. -/
theorem exists_eventuallyEq_unique_local_solution_holomorphic_system {n : ℕ}
    {Ω : Set (ℂ × (Fin n → ℂ))} {f : ℂ → (Fin n → ℂ) → Fin n → ℂ} {b : Fin n → ℂ}
    (hΩ : IsOpen Ω) (h0 : ((0 : ℂ), b) ∈ Ω)
    (hf : AnalyticOnNhd ℂ (fun p : ℂ × (Fin n → ℂ) ↦ f p.1 p.2) Ω) :
    ∃ U : Set ℂ, ∃ φ : ℂ → Fin n → ℂ,
      IsHolomorphicSystemSolutionOn Ω f 0 b U φ ∧
      ∀ V : Set ℂ, ∀ ψ : ℂ → Fin n → ℂ,
        IsHolomorphicSystemSolutionOn Ω f 0 b V ψ →
        ψ =ᶠ[𝓝 (0 : ℂ)] φ := by
  rcases unique_local_solution_holomorphic_system hΩ h0 hf with ⟨φ, hφ, huniq⟩
  rcases hφ with ⟨U, ψ, hψ, hψφ⟩
  refine ⟨U, ψ, hψ, ?_⟩
  intro V χ hχ
  have hχ' : IsHolomorphicSystemSolution Ω f 0 b (χ : Germ (𝓝 (0 : ℂ)) (Fin n → ℂ)) :=
    hχ.isHolomorphicSystemSolution
  exact Germ.coe_eq.mp <| (huniq _ hχ').trans hψφ.symm
