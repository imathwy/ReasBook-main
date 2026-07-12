import ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_22

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u

variable {Ω : Type u}

/-- Helper for Theorem 5.23: the open empirical cdf averages the indicators of the strict lower
intervals `(-∞, x)`. -/
private noncomputable def openEmpiricalDistributionFunction {n : ℕ}
    (X : Fin (n + 1) → Ω → ℝ) : Ω → ℝ → ℝ :=
  fun ω x ↦
    (∑ i : Fin (n + 1), if X i ω < x then (1 : ℝ) else 0) / (n + 1 : ℝ)

/-- Helper for Theorem 5.23: the open empirical cdf is the empirical average of the strict
lower-interval indicators. -/
private theorem openEmpiricalDistributionFunction_apply {n : ℕ}
    (X : Fin (n + 1) → Ω → ℝ) (ω : Ω) (x : ℝ) :
    openEmpiricalDistributionFunction X ω x =
      (∑ i : Fin (n + 1), if X i ω < x then (1 : ℝ) else 0) / (n + 1 : ℝ) :=
  rfl

variable [MeasurableSpace Ω]

/-- Helper for Theorem 5.23: the left limit of the cdf of a real random variable is the open-ray
probability `P[Y < x]`. -/
private theorem cdf_leftLim_eq_real_preimage_Iio
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : Measurable Y) (x : ℝ) :
    Function.leftLim (cdf (P.map Y)) x = P.real (Y ⁻¹' Set.Iio x) := by
  have hprob : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hmeasure : (cdf (P.map Y)).measure (Set.Iio x) = P.map Y (Set.Iio x) := by
    -- Proof comment: the cdf of `P.map Y` reconstructs the pushed-forward measure.
    simpa using congrArg (fun μ : Measure ℝ ↦ μ (Set.Iio x))
      (measure_cdf (P.map Y))
  have hleft :
      (cdf (P.map Y)).measure (Set.Iio x) = ENNReal.ofReal (Function.leftLim (cdf (P.map Y)) x) := by
    -- Proof comment: the Stieltjes-measure formula for `Iio` identifies the open ray with the
    -- left limit because the cdf starts at `0` at `-∞`.
    simpa [sub_zero] using (cdf (P.map Y)).measure_Iio (tendsto_cdf_atBot (P.map Y)) x
  calc
    Function.leftLim (cdf (P.map Y)) x = ((cdf (P.map Y)).measure (Set.Iio x)).toReal := by
      have hleft_nonneg : 0 ≤ Function.leftLim (cdf (P.map Y)) x := by
        obtain ⟨y, hy⟩ := exists_lt x
        exact le_trans (cdf_nonneg (P.map Y) y) ((monotone_cdf (P.map Y)).le_leftLim hy)
      have hleft_toReal := congrArg ENNReal.toReal hleft
      simpa [hleft_nonneg] using hleft_toReal.symm
    _ = P.real (Y ⁻¹' Set.Iio x) := by
      rw [hmeasure, Measure.real_def,
        Measure.map_apply_of_aemeasurable hY.aemeasurable measurableSet_Iio]

/-- Helper for Theorem 5.23: at a fixed point `x`, the shifted closed and open empirical cdfs
converge almost surely to `F(x)` and `F(x-)`, respectively. -/
private theorem ae_tendsto_empirical_cdf_at_point
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P) (x : ℝ) :
    ∀ᵐ ω ∂P,
      Tendsto
          (fun n ↦ empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x)
          atTop (𝓝 (cdf (P.map (X 1)) x)) ∧
        Tendsto
          (fun n ↦ openEmpiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x)
          atTop (𝓝 (Function.leftLim (cdf (P.map (X 1))) x)) := by
  let F : ℝ → ℝ := cdf (P.map (X 1))
  let Fc : ℝ → ℝ := Set.indicator (Set.Iic x) (fun _ ↦ (1 : ℝ))
  let Fo : ℝ → ℝ := Set.indicator (Set.Iio x) (fun _ ↦ (1 : ℝ))
  let Yc : ℕ → Ω → ℝ := fun n ↦ Fc ∘ X (n + 1)
  let Yo : ℕ → Ω → ℝ := fun n ↦ Fo ∘ X (n + 1)
  have hX1_ae : AEMeasurable (X 1) P := (hX_iid.identDistrib 0 0).aemeasurable_fst
  let X1m : Ω → ℝ := hX1_ae.mk (X 1)
  have hX1m_ae : X1m =ᵐ[P] X 1 := hX1_ae.ae_eq_mk.symm
  haveI : IsProbabilityMeasure (P.map (X 1)) := Measure.isProbabilityMeasure_map hX1_ae
  haveI : IsProbabilityMeasure (P.map X1m) :=
    Measure.isProbabilityMeasure_map hX1_ae.measurable_mk.aemeasurable
  have hFc_meas : Measurable Fc := by
    -- Proof comment: the closed-ray indicator is measurable.
    exact (measurable_indicator_const_iff (1 : ℝ)).2 measurableSet_Iic
  have hFo_meas : Measurable Fo := by
    -- Proof comment: the open-ray indicator is measurable.
    exact (measurable_indicator_const_iff (1 : ℝ)).2 measurableSet_Iio
  have hYc_integrable : Integrable (Yc 0) P := by
    -- Proof comment: the closed indicator is a bounded simple function, hence integrable after
    -- composition with `X₁`.
    have hmk :
        Integrable
          ((SimpleFunc.piecewise (Set.Iic x) measurableSet_Iic
            (SimpleFunc.const ℝ (1 : ℝ)) (SimpleFunc.const ℝ (0 : ℝ))).comp X1m
              hX1_ae.measurable_mk) P :=
      SimpleFunc.integrable_of_isFiniteMeasure
        ((SimpleFunc.piecewise (Set.Iic x) measurableSet_Iic
          (SimpleFunc.const ℝ (1 : ℝ)) (SimpleFunc.const ℝ (0 : ℝ))).comp X1m
            hX1_ae.measurable_mk)
    refine hmk.congr ?_
    simpa [Yc, Fc, X1m] using (hX1m_ae.fun_comp Fc)
  have hYo_integrable : Integrable (Yo 0) P := by
    -- Proof comment: the open indicator is handled in the same way.
    have hmk :
        Integrable
          ((SimpleFunc.piecewise (Set.Iio x) measurableSet_Iio
            (SimpleFunc.const ℝ (1 : ℝ)) (SimpleFunc.const ℝ (0 : ℝ))).comp X1m
              hX1_ae.measurable_mk) P :=
      SimpleFunc.integrable_of_isFiniteMeasure
        ((SimpleFunc.piecewise (Set.Iio x) measurableSet_Iio
          (SimpleFunc.const ℝ (1 : ℝ)) (SimpleFunc.const ℝ (0 : ℝ))).comp X1m
            hX1_ae.measurable_mk)
    refine hmk.congr ?_
    simpa [Yo, Fo, X1m] using (hX1m_ae.fun_comp Fo)
  have hYc_iIndep : iIndepFun Yc P := by
    -- Proof comment: independence is preserved under measurable postcomposition.
    exact hX_iid.iIndepFun.comp (fun _ ↦ Fc) fun _ ↦ hFc_meas
  have hYo_iIndep : iIndepFun Yo P := by
    -- Proof comment: the same measurable postcomposition argument works for the open indicators.
    exact hX_iid.iIndepFun.comp (fun _ ↦ Fo) fun _ ↦ hFo_meas
  have hYc_ident : ∀ n, IdentDistrib (Yc n) (Yc 0) P P := by
    -- Proof comment: all shifted closed indicators have the same distribution because the
    -- underlying sequence is identically distributed.
    intro n
    exact (hX_iid.identDistrib n 0).comp hFc_meas
  have hYo_ident : ∀ n, IdentDistrib (Yo n) (Yo 0) P P := by
    -- Proof comment: likewise for the open indicators.
    intro n
    exact (hX_iid.identDistrib n 0).comp hFo_meas
  have hYc_limit :
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, Yc i ω) / n) atTop (𝓝 P[Yc 0]) := by
    exact strong_law_ae_real Yc hYc_integrable
      (fun i j hij ↦ hYc_iIndep.indepFun hij) hYc_ident
  have hYo_limit :
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, Yo i ω) / n) atTop (𝓝 P[Yo 0]) := by
    exact strong_law_ae_real Yo hYo_integrable
      (fun i j hij ↦ hYo_iIndep.indepFun hij) hYo_ident
  have hYc_expectation : P[Yc 0] = F x := by
    -- Proof comment: the expectation of the closed indicator is exactly the cdf value `F(x)`.
    calc
      P[Yc 0] = ∫ ω, Fc (X 1 ω) ∂P := by
        rfl
      _ = ∫ y, Fc y ∂(P.map (X 1)) := by
        rw [integral_map hX1_ae hFc_meas.aestronglyMeasurable]
      _ = (P.map (X 1)).real (Set.Iic x) := by
        simp [Fc, integral_indicator_const, measurableSet_Iic, smul_eq_mul]
      _ = F x := by
        simpa [F] using (cdf_eq_real (P.map (X 1)) x).symm
  have hYo_expectation : P[Yo 0] = Function.leftLim F x := by
    -- Proof comment: the expectation of the open indicator is the left limit `F(x-)`.
    have hmap : P.map X1m = P.map (X 1) := by
      simpa [X1m] using (Measure.map_congr hX1_ae.ae_eq_mk).symm
    calc
      P[Yo 0] = ∫ ω, Fo (X 1 ω) ∂P := by
        rfl
      _ = ∫ y, Fo y ∂(P.map (X 1)) := by
        rw [integral_map hX1_ae hFo_meas.aestronglyMeasurable]
      _ = (P.map (X 1)).real (Set.Iio x) := by
        simp [Fo, integral_indicator_const, measurableSet_Iio, smul_eq_mul]
      _ = Function.leftLim F x := by
        calc
          (P.map (X 1)).real (Set.Iio x) = (P.map X1m).real (Set.Iio x) := by
            rw [hmap]
          _ = P.real (X1m ⁻¹' Set.Iio x) := by
            have happly :
                P.map X1m (Set.Iio x) = P (X1m ⁻¹' Set.Iio x) :=
              Measure.map_apply hX1_ae.measurable_mk measurableSet_Iio
            simpa [Measure.real_def] using congrArg ENNReal.toReal happly
          _ = Function.leftLim (cdf (P.map X1m)) x := by
            exact (cdf_leftLim_eq_real_preimage_Iio P hX1_ae.measurable_mk x).symm
          _ = Function.leftLim F x := by
            simp [F, hmap]
  filter_upwards [hYc_limit, hYo_limit] with ω hωc hωo
  constructor
  · -- Proof comment: reindex the strong-law averages from `range n` to the empirical cdf with
    -- sample size `n + 1`.
    have hshift :
        Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range (n + 1), Yc i ω) / (n + 1 : ℝ)) atTop
          (𝓝 P[Yc 0]) := by
      convert hωc.comp (tendsto_add_atTop_nat 1) using 1
      ext n
      simp
    refine Tendsto.congr' ?_ (hYc_expectation ▸ hshift)
    refine Filter.Eventually.of_forall fun n ↦ ?_
    have hsum :
        ∑ i ∈ Finset.range (n + 1), Yc i ω =
          ∑ i ∈ Finset.range (n + 1), if X (i + 1) ω ≤ x then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hix : X (i + 1) ω ≤ x
      · simp [Yc, Fc, hix]
      · simp [Yc, Fc, hix]
    calc
      (∑ i ∈ Finset.range (n + 1), Yc i ω) / (n + 1 : ℝ) =
          (∑ i ∈ Finset.range (n + 1), if X (i + 1) ω ≤ x then (1 : ℝ) else 0) / (n + 1 : ℝ) := by
        rw [hsum]
      _ =
          (∑ i : Fin (n + 1), if X (i.1 + 1) ω ≤ x then (1 : ℝ) else 0) / (n + 1 : ℝ) := by
        rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ if X (i + 1) ω ≤ x then (1 : ℝ) else 0)
          (n + 1)]
      _ = empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x := by
        simpa using
          (empiricalDistributionFunction_apply (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x).symm
  · -- Proof comment: the same reindexing turns the open averages into the strict empirical cdf.
    have hshift :
        Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range (n + 1), Yo i ω) / (n + 1 : ℝ)) atTop
          (𝓝 P[Yo 0]) := by
      convert hωo.comp (tendsto_add_atTop_nat 1) using 1
      ext n
      simp
    refine Tendsto.congr' ?_ (hYo_expectation ▸ hshift)
    refine Filter.Eventually.of_forall fun n ↦ ?_
    have hsum :
        ∑ i ∈ Finset.range (n + 1), Yo i ω =
          ∑ i ∈ Finset.range (n + 1), if X (i + 1) ω < x then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hix : X (i + 1) ω < x
      · simp [Yo, Fo, hix]
      · simp [Yo, Fo, hix]
    calc
      (∑ i ∈ Finset.range (n + 1), Yo i ω) / (n + 1 : ℝ) =
          (∑ i ∈ Finset.range (n + 1), if X (i + 1) ω < x then (1 : ℝ) else 0) / (n + 1 : ℝ) := by
        rw [hsum]
      _ =
          (∑ i : Fin (n + 1), if X (i.1 + 1) ω < x then (1 : ℝ) else 0) / (n + 1 : ℝ) := by
        rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ if X (i + 1) ω < x then (1 : ℝ) else 0)
          (n + 1)]
      _ = openEmpiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x := by
        simpa using
          (openEmpiricalDistributionFunction_apply (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x).symm

/-- Helper for Theorem 5.23: on every finite grid of real points, the shifted closed and open
empirical cdfs converge almost surely and simultaneously at all grid points. -/
private theorem ae_tendsto_empirical_cdf_on_finite_grid
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P) (s : Finset ℝ) :
    ∀ᵐ ω ∂P,
      ∀ x ∈ s,
        Tendsto
            (fun n ↦ empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x)
            atTop (𝓝 (cdf (P.map (X 1)) x)) ∧
          Tendsto
            (fun n ↦ openEmpiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x)
            atTop (𝓝 (Function.leftLim (cdf (P.map (X 1))) x)) := by
  have hattach :
      ∀ᵐ ω ∂P, ∀ y : s,
        Tendsto
            (fun n ↦ empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω y.1)
            atTop (𝓝 (cdf (P.map (X 1)) y.1)) ∧
          Tendsto
            (fun n ↦ openEmpiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω y.1)
            atTop (𝓝 (Function.leftLim (cdf (P.map (X 1))) y.1)) := by
    -- Proof comment: intersect the finitely many almost-sure events by quantifying over the
    -- attached finite type.
    rw [ae_all_iff]
    intro y
    simpa using ae_tendsto_empirical_cdf_at_point P X hX_iid y.1
  filter_upwards [hattach] with ω hω x hx
  simpa using hω ⟨x, hx⟩

/-- Helper for Theorem 5.23: every interior level `t ∈ (0,1)` admits a real quantile point
`q` with `F(q-) ≤ t ≤ F(q)`. -/
private theorem exists_stieltjes_quantile
    (F : StieltjesFunction ℝ) (hbot : Tendsto F atBot (𝓝 0))
    (htop : Tendsto F atTop (𝓝 1)) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ q : ℝ, Function.leftLim F q ≤ t ∧ t ≤ F q := by
  let S : Set ℝ := {x | t ≤ F x}
  have hS_nonempty : S.Nonempty := by
    -- Proof comment: because `F(x) → 1` at `+∞`, some point has cdf value at least `t`.
    have hmem : Set.Ioi t ∈ 𝓝 (1 : ℝ) := Ioi_mem_nhds ht1
    have h_eventually : ∀ᶠ x in atTop, t < F x := htop hmem
    obtain ⟨x, hx⟩ := h_eventually.exists
    exact ⟨x, le_of_lt hx⟩
  have hS_bddBelow : BddBelow S := by
    -- Proof comment: because `F(x) → 0` at `-∞`, points with cdf value strictly below `t`
    -- provide lower bounds for the superlevel set `S`.
    have hhalf : 0 < t / 2 := by
      linarith
    have hmem : Set.Iio (t / 2) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hhalf
    have h_eventually : ∀ᶠ x in atBot, F x < t / 2 := hbot hmem
    obtain ⟨x, hx⟩ := h_eventually.exists
    refine ⟨x, ?_⟩
    intro y hy
    by_contra hxy
    have hyx : y < x := lt_of_not_ge hxy
    have hxlt : F x < t := by
      linarith
    exact absurd hxlt (not_lt_of_ge (le_trans hy (F.mono (le_of_lt hyx))))
  let q : ℝ := sInf S
  refine ⟨q, ?_, ?_⟩
  · -- Proof comment: if the left limit were above `t`, some point strictly left of `q` would
    -- already lie in the superlevel set, contradicting the infimum property of `q`.
    rw [Monotone.leftLim_eq_sSup F.mono (by infer_instance : NeBot (𝓝[<] q)).ne]
    refine csSup_le ?_ ?_
    · rcases exists_lt q with ⟨x, hx⟩
      exact ⟨F x, ⟨x, hx, rfl⟩⟩
    · rintro _ ⟨x, hxlt, rfl⟩
      by_cases hxt : t ≤ F x
      · have hq_le : q ≤ x := csInf_le hS_bddBelow hxt
        exact False.elim (absurd hxlt (not_lt_of_ge hq_le))
      · exact le_of_lt (lt_of_not_ge hxt)
  · -- Proof comment: right continuity at the infimum sends `q` into the infimum of the image of
    -- the superlevel set, and every point in that image is at least `t`.
    have hcont : ContinuousWithinAt F S q := by
      refine (F.right_continuous q).mono ?_
      intro x hx
      exact csInf_le hS_bddBelow hx
    have hq : F q = sInf (F '' S) :=
      MonotoneOn.map_csInf_of_continuousWithinAt hcont (F.mono.monotoneOn S) hS_nonempty
        hS_bddBelow
    have hlower : t ≤ sInf (F '' S) := by
      refine le_csInf ?_ ?_
      · rcases hS_nonempty with ⟨x, hx⟩
        exact ⟨F x, ⟨x, hx, rfl⟩⟩
      · rintro _ ⟨x, hx, rfl⟩
        exact hx
    simpa [q, hq] using hlower

/-- Helper for Theorem 5.23: for every positive mesh size `1 / N`, the cdf has real left and
right tail cutoffs whose masses are at most `1 / N`. -/
private theorem exists_cdf_tail_cutoffs
    (F : StieltjesFunction ℝ) (hbot : Tendsto F atBot (𝓝 0))
    (htop : Tendsto F atTop (𝓝 1)) (N : ℕ) (hN : 0 < N) :
    ∃ a b : ℝ, F a ≤ (1 : ℝ) / N ∧ 1 - (1 : ℝ) / N ≤ F b := by
  have hN_real : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hleft_mem : Set.Iio ((1 : ℝ) / N) ∈ 𝓝 (0 : ℝ) := by
    apply Iio_mem_nhds
    exact one_div_pos.mpr hN_real
  have hright_mem : Set.Ioi (1 - (1 : ℝ) / N) ∈ 𝓝 (1 : ℝ) := by
    apply Ioi_mem_nhds
    linarith [one_div_pos.mpr hN_real]
  have hleft_eventually : ∀ᶠ x in atBot, F x < (1 : ℝ) / N := hbot hleft_mem
  have hright_eventually : ∀ᶠ x in atTop, 1 - (1 : ℝ) / N < F x := htop hright_mem
  obtain ⟨a, ha⟩ := hleft_eventually.exists
  obtain ⟨b, hb⟩ := hright_eventually.exists
  -- Proof comment: the tail estimates come directly from the cdf limits at `±∞`.
  exact ⟨a, b, ha.le, hb.le⟩

-- Proof sketch: for each fixed `x`, apply the strong law of large numbers to the indicator
-- variables of the events `X_i <= x` and `X_i < x` to get almost
-- sure convergence of the empirical cdf at the finitely many quantile points used in the standard
-- proof. Those quantile controls imply that the Kolmogorov distance between the empirical
-- distribution function and the common cdf has almost-sure `limsup` equal to `0`.
/-- Theorem 5.23: Glivenko--Cantelli. For an i.i.d. real sequence `X_1, X_2, ...`, the Kolmogorov
distance between the empirical distribution function `F_n` and the common distribution function
`F` has almost-sure `limsup` equal to `0`. -/
theorem glivenko_cantelli_ae
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P) :
    ∀ᵐ ω ∂P,
      limsup
        (fun n ↦
          sSup <|
            Set.range fun x ↦
              |empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x -
                cdf (P.map (X 1)) x|) atTop = 0 := by
  let F := cdf (P.map (X 1))
  -- Proof comment: the target route is still the textbook one. The helpers above already isolate
  -- the strict-open empirical cdf and the identity `F(x-) = P[X₁ < x]`, which are the two
  -- measure-theoretic ingredients needed for the quantile-grid argument.
  have hfinite_grid :
      ∀ s : Finset ℝ, ∀ᵐ ω ∂P,
        ∀ x ∈ s,
          Tendsto
              (fun n ↦ empiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x)
              atTop (𝓝 (F x)) ∧
            Tendsto
              (fun n ↦ openEmpiricalDistributionFunction (fun i : Fin (n + 1) ↦ X (i.1 + 1)) ω x)
              atTop (𝓝 (Function.leftLim F x)) := by
    intro s
    simpa [F] using ae_tendsto_empirical_cdf_on_finite_grid P X hX_iid s
  have hquantile :
      ∀ {t : ℝ}, 0 < t → t < 1 → ∃ q : ℝ, Function.leftLim F q ≤ t ∧ t ≤ F q := by
    intro t ht0 ht1
    -- Proof comment: the cdf-specific quantile points come from the generic Stieltjes quantile
    -- lemma applied to `F`.
    exact exists_stieltjes_quantile F (tendsto_cdf_atBot (P.map (X 1)))
      (tendsto_cdf_atTop (P.map (X 1))) ht0 ht1
  have htail_cutoffs :
      ∀ N : ℕ, 0 < N → ∃ a b : ℝ, F a ≤ (1 : ℝ) / N ∧ 1 - (1 : ℝ) / N ≤ F b := by
    intro N hN
    -- Proof comment: the outer tails are already controlled by the cdf limits at `±∞`.
    exact exists_cdf_tail_cutoffs F (tendsto_cdf_atBot (P.map (X 1)))
      (tendsto_cdf_atTop (P.map (X 1))) N hN
  -- Route correction: the shifted strong-law package is now in place as `hfinite_grid`; the
  -- remaining work is to assemble the individual quantile/tail points into one monotone finite
  -- grid and then prove the deterministic interval-by-interval domination of the Kolmogorov
  -- distance by the corresponding finite-grid error term.
  -- TODO: combine `hquantile` and `htail_cutoffs` into a monotone grid `x₀ < ... < x_N`, define
  -- the error `Rₙ`, and prove `sSup (Set.range ...) ≤ Rₙ + 1 / N` before taking the limsup.
  sorry
