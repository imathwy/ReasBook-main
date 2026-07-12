import DifferentialForms_Cartan_1970.IV.section17.«0002_Theorem_IV_5_extra_2».ParametricPowerSeries

/-- Helper for Theorem IV.5-extra-2: on the quarter-radius ball around `w0`, the shifted monomial
is bounded by the corresponding half-radius geometric factor. -/
lemma norm_sub_pow_le_halfRadius_geometric
    {w w0 : ℂ} {ρ : ℝ} (hρpos : 0 < ρ) (n : ℕ)
    (hw : w ∈ Metric.ball w0 (ρ / 4)) :
    ‖(w - w0) ^ n‖ ≤ (ρ / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n := by
  have hw_norm : ‖w - w0‖ < ρ / 4 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  calc
    ‖(w - w0) ^ n‖ = ‖w - w0‖ ^ n := by rw [norm_pow]
    _ ≤ (ρ / 4) ^ n := by
          exact pow_le_pow_left₀ (a := ‖w - w0‖) (b := ρ / 4) (by positivity) hw_norm.le n
    _ = (ρ / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n := by
          rw [← mul_pow]
          ring

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: a geometric coefficient bound at
radius `ρ / 2` and the quarter-radius bound on the shifted monomial combine into the final
`(1 / 2)^n` majorant for the normalized Cauchy term. -/
lemma norm_weightedCauchyTerm_le_geometric_of_coeffBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : ℕ → E → ℂ} {w0 : ℂ} {ρ C : ℝ} (hρpos : 0 < ρ)
    {p : E × ℂ} (hpLast : p.2 ∈ Metric.ball w0 (ρ / 4))
    (hCnonneg : 0 ≤ C)
    (hCoeff : ∀ n : ℕ, ‖A n p.1‖ ≤ C / (ρ / 2 : ℝ) ^ n) :
    ∀ n : ℕ, ‖A n p.1 * (p.2 - w0) ^ n‖ ≤ C * (1 / 2 : ℝ) ^ n := by
  intro n
  have hρhalf_ne : (ρ / 2 : ℝ) ≠ 0 := by
    linarith [hρpos]
  have hCoeffBudgetNonneg : 0 ≤ C / (ρ / 2 : ℝ) ^ n := by
    positivity
  have hLastFactor :
      ‖(p.2 - w0) ^ n‖ ≤ (ρ / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n :=
    norm_sub_pow_le_halfRadius_geometric hρpos n hpLast
  calc
    ‖A n p.1 * (p.2 - w0) ^ n‖ = ‖A n p.1‖ * ‖(p.2 - w0) ^ n‖ := by
      rw [norm_mul]
    _ ≤ (C / (ρ / 2 : ℝ) ^ n) * ‖(p.2 - w0) ^ n‖ := by
          exact mul_le_mul_of_nonneg_right (hCoeff n) (norm_nonneg _)
    _ ≤ (C / (ρ / 2 : ℝ) ^ n) * ((ρ / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n) := by
          exact mul_le_mul_of_nonneg_left hLastFactor hCoeffBudgetNonneg
    _ = C * (1 / 2 : ℝ) ^ n := by
          field_simp [pow_ne_zero n hρhalf_ne]

/-- Helper for Theorem IV.5-extra-2: pointwise analytic germs along a set already give the
corresponding continuity owner on that set. -/
lemma continuousOn_of_forall_analyticAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {s : Set E} {f : E → F}
    (hanalytic : ∀ x ∈ s, AnalyticAt ℂ f x) :
    ContinuousOn f s := by
  intro x hx
  exact (hanalytic x hx).continuousAt.continuousWithinAt

/-- Helper for Theorem IV.5-extra-2: the scalar `sum` attached to a `cauchyPowerSeries` is the
usual coefficient `tsum` in powers of the evaluation variable. -/
lemma cauchyPowerSeries_sum_eq_tsum_coeff
    {F : ℂ → ℂ} {w0 δ : ℂ} {R : ℝ} :
    (cauchyPowerSeries F w0 R).sum δ =
      ∑' n : ℕ, (cauchyPowerSeries F w0 R).coeff n * δ ^ n := by
  rw [FormalMultilinearSeries.sum]
  refine tsum_congr fun n ↦ ?_
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp [smul_eq_mul, mul_comm]

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: once the coefficient family is
analytic on the transported open block ball and satisfies the pointwise geometric Cauchy bound
there, shrinking to the fixed smaller closed ball packages exactly the closed-ball continuity and
pointwise bound data used at the normalized-series closeout. -/
lemma transportedCoeff_packageOnClosedSmallBall_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : ℕ → E → ℂ} {x0 : E} {r0 R : ℝ} (hr0pos : 0 < r0)
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r0))
    (hCoeffBound :
      ∀ x ∈ Metric.ball x0 r0, ∃ Cx : ℝ, 0 ≤ Cx ∧
        ∀ n : ℕ, ‖A n x‖ ≤ Cx / R ^ n) :
    let r1 : ℝ := r0 / 2
    (∀ n : ℕ, ContinuousOn (A n) (Metric.closedBall x0 r1)) ∧
      ∀ x ∈ Metric.closedBall x0 r1, ∃ Cx : ℝ, 0 ≤ Cx ∧
        ∀ n : ℕ, ‖A n x‖ ≤ Cx / R ^ n := by
  let r1 : ℝ := r0 / 2
  have hr1lt : r1 < r0 := by
    dsimp [r1]
    linarith
  exact
    localCoeffPackageOnClosedBall_of_openBall
      (x0 := x0) (r₁ := r1) (r₂ := r0) (R := R) hr1lt hCoeffOn hCoeffBound

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: on a compact closed ball, an explicit
continuous coefficient budget function can be replaced by one global geometric constant. This is
the correct compact-uniformization surface for later Cauchy-row bounds; a bare pointwise
`∃ Cx` package is not enough. -/
lemma uniformGeometricCoeffBoundOnClosedBall_of_continuousBound_local
    {E : Type*} [PseudoMetricSpace E] [ProperSpace E]
    {A : ℕ → E → ℂ} {x0 : E} {r R : ℝ} {B : E → ℝ}
    (hR : 0 < R)
    (hBcont : ContinuousOn B (Metric.closedBall x0 r))
    (hCoeff :
      ∀ x ∈ Metric.closedBall x0 r, ∀ n : ℕ, ‖A n x‖ ≤ B x / R ^ n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall x0 r, ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n := by
  obtain ⟨M, hMbound⟩ :=
    (isCompact_closedBall x0 r).exists_bound_of_continuousOn (f := B) hBcont
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro x hx n
  have hBx : B x ≤ max M 0 := by
    exact le_trans (le_abs_self _) (le_trans (hMbound x hx) (le_max_left _ _))
  have hRpow_nonneg : 0 ≤ R ^ n := by
    positivity
  -- Freeze the compact sup bound for `B` once, then divide through the positive radius factor.
  calc
    ‖A n x‖ ≤ B x / R ^ n := hCoeff x hx n
    _ ≤ max M 0 / R ^ n := by
          exact div_le_div_of_nonneg_right hBx hRpow_nonneg
