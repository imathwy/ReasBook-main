import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_33

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u}

/-- The `n`th arrival time attached to a `0`-indexed interarrival sequence `W`, defined as the sum
`W 0 + ⋯ + W (n - 1)`. This is the chapter's canonical `0`-indexed version of the textbook
partial-sum arrival times. -/
def arrivalTime (W : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  ∑ i ∈ Finset.range n, W i

/-- The initial arrival time is `0`. -/
@[simp] theorem arrivalTime_zero (W : ℕ → Ω → ℝ) : arrivalTime W 0 = 0 := by
  simp [arrivalTime]

/-- The next arrival time is obtained by adding the next interarrival time. -/
@[simp] theorem arrivalTime_succ (W : ℕ → Ω → ℝ) (n : ℕ) :
    arrivalTime W (n + 1) = arrivalTime W n + W n := by
  simp [arrivalTime, Finset.sum_range_succ]

/-- Helper for Theorem 5.36: splitting at time `m`, the later arrival time `T_(m+n)` is the
initial prefix `T_m` plus the sum over the contiguous block of interarrivals starting at `m`. -/
theorem arrivalTime_add (W : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω) :
    arrivalTime W (m + n) ω = arrivalTime W m ω + ∑ i ∈ Finset.range n, W (m + i) ω := by
  -- Proof comment: split the partial sum at the index `m` using the standard `sum_range_add`
  -- decomposition.
  rw [arrivalTime, Finset.sum_range_add]
  simp [arrivalTime]

/-- The renewal counting process associated with an interarrival sequence `W`, defined by the
textbook infimum count for the first arrival time that strictly exceeds `t`. Since `Nat.sInf`
already sends the empty set to `0`, no extra wrapper-level totalization is needed in the public
definition; the genuine renewal-path hypotheses enter only in the companion specification lemmas
below. -/
noncomputable def renewalCountingProcess (W : ℕ → Ω → ℝ) : NNReal → Ω → ℕ :=
  by
    classical
    exact fun t ω ↦ sInf { n : ℕ | t < arrivalTime W (n + 1) ω }

/-- The public renewal counting process is exactly the textbook `sInf` count. -/
@[simp] theorem renewalCountingProcess_eq_sInf
    (W : ℕ → Ω → ℝ) (t : NNReal) (ω : Ω) :
    renewalCountingProcess W t ω = sInf { n : ℕ | t < arrivalTime W (n + 1) ω } := by
  classical
  rfl

/-- If the arrival times along a sample path diverge to `∞`, then `renewalCountingProcess W t ω`
is characterized by the usual inequalities `T_N(ω) ≤ t < T_(N+1)(ω)`. This is the public bridge
from the concrete `sInf`-definition to the textbook renewal-count inequalities. -/
theorem renewalCountingProcess_spec
    (W : ℕ → Ω → ℝ) {t : NNReal} {ω : Ω}
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) :
    arrivalTime W (renewalCountingProcess W t ω) ω ≤ t ∧
      t < arrivalTime W (renewalCountingProcess W t ω + 1) ω := by
  classical
  let S : Set ℕ := {n : ℕ | t < arrivalTime W (n + 1) ω}
  have hS_nonempty : S.Nonempty := by
    -- Divergence of the arrival times guarantees that some arrival strictly exceeds `t`.
    have h_arrival_tendsto' := h_arrival_tendsto
    rw [Filter.tendsto_atTop_atTop] at h_arrival_tendsto'
    rcases h_arrival_tendsto' ((t : ℝ) + 1) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    change t < arrivalTime W (N + 1) ω
    have h_bound : (t : ℝ) + 1 ≤ arrivalTime W (N + 1) ω :=
      hN (N + 1) (Nat.le_succ N)
    linarith
  have h_eq :
      renewalCountingProcess W t ω = sInf S := by
    simp [S]
  refine ⟨?_, ?_⟩
  · -- Minimality of the `sInf` index forces the preceding arrival time to stay below `t`.
    rw [h_eq]
    by_cases hzero : sInf S = 0
    · simp [hzero, arrivalTime_zero]
    · have hsInf_pos : 0 < sInf S := Nat.pos_of_ne_zero hzero
      have h_prev_not_mem : sInf S - 1 ∉ S :=
        Nat.notMem_of_lt_sInf (Nat.pred_lt hzero)
      have h_le : arrivalTime W (sInf S) ω ≤ t := by
        by_contra h_gt
        have h_prev_mem : sInf S - 1 ∈ S := by
          change t < arrivalTime W (sInf S - 1 + 1) ω
          rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hsInf_pos)]
          exact lt_of_not_ge h_gt
        exact h_prev_not_mem h_prev_mem
      simpa using h_le
  · -- Membership of the minimizing index in the defining set gives the upper strict inequality.
    rw [h_eq]
    have h_mem : sInf S ∈ S := Nat.sInf_mem hS_nonempty
    simpa [S] using h_mem

/-- On a sample path whose first arrival is strictly after `0`, the renewal counting process starts
from `0`. -/
theorem renewalCountingProcess_zero
    (W : ℕ → Ω → ℝ) (ω : Ω)
    (h_first_arrival : 0 < arrivalTime W 1 ω) :
    renewalCountingProcess W 0 ω = 0 := by
  classical
  rw [renewalCountingProcess_eq_sInf]
  apply Nat.sInf_eq_zero.2
  left
  rw [Set.mem_setOf_eq]
  simpa using h_first_arrival

/-- Helper for Theorem 5.36: on a genuine renewal path, the counting process is monotone in time.
-/
theorem renewalCountingProcess_mono
    (W : ℕ → Ω → ℝ) {ω : Ω}
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop) :
    Monotone (fun t : NNReal ↦ renewalCountingProcess W t ω) := by
  intro s t hst
  let S : NNReal → Set ℕ := fun r ↦ {n : ℕ | r < arrivalTime W (n + 1) ω}
  have hs_eq :
      renewalCountingProcess W s ω = sInf (S s) := by
    simp [S]
  have hspec_t :
      arrivalTime W (renewalCountingProcess W t ω) ω ≤ t ∧
        t < arrivalTime W (renewalCountingProcess W t ω + 1) ω :=
    renewalCountingProcess_spec W h_arrival_tendsto
  -- Proof comment: the first arrival strictly above `t` is also strictly above every earlier time `s`.
  change renewalCountingProcess W s ω ≤ renewalCountingProcess W t ω
  rw [hs_eq]
  apply Nat.sInf_le
  show renewalCountingProcess W t ω ∈ S s
  show s < arrivalTime W (renewalCountingProcess W t ω + 1) ω
  exact lt_of_le_of_lt hst hspec_t.2

/-- Helper for Theorem 5.36: on a genuine renewal path, the counting process equals `n` exactly on
the strip `T_n ≤ t < T_(n+1)`. -/
theorem renewalCountingProcess_eq_iff_arrival_strip
    (W : ℕ → Ω → ℝ) {t : NNReal} {ω : Ω} {n : ℕ}
    (h_arrival_strict : StrictMono (fun m ↦ arrivalTime W m ω))
    (h_arrival_tendsto : Tendsto (fun m ↦ arrivalTime W m ω) atTop atTop) :
    renewalCountingProcess W t ω = n ↔
      arrivalTime W n ω ≤ t ∧ t < arrivalTime W (n + 1) ω := by
  constructor
  · intro hn
    -- Proof comment: substitute the claimed count into the public strip specification.
    have hspec :
        arrivalTime W (renewalCountingProcess W t ω) ω ≤ t ∧
          t < arrivalTime W (renewalCountingProcess W t ω + 1) ω :=
      renewalCountingProcess_spec W h_arrival_tendsto
    rw [hn] at hspec
    exact hspec
  · intro ht_strip
    rcases ht_strip with ⟨ht_lower, ht_upper⟩
    let S : Set ℕ := {m : ℕ | t < arrivalTime W (m + 1) ω}
    have hs_eq :
        renewalCountingProcess W t ω = sInf S := by
      simp [S]
    have hn_mem : n ∈ S := by
      show t < arrivalTime W (n + 1) ω
      exact ht_upper
    have hsInf_le : sInf S ≤ n := Nat.sInf_le hn_mem
    have hsInf_mem : sInf S ∈ S := Nat.sInf_mem ⟨n, hn_mem⟩
    have hn_le : n ≤ sInf S := by
      refine Nat.le_of_not_lt ?_
      intro hsInf_lt
      have hstep_le :
          arrivalTime W (sInf S + 1) ω ≤ arrivalTime W n ω :=
        h_arrival_strict.monotone (Nat.succ_le_of_lt hsInf_lt)
      exact not_lt_of_ge (le_trans hstep_le ht_lower) hsInf_mem
    -- Proof comment: `n` is both an upper and a lower bound for the defining `sInf`.
    rw [hs_eq]
    exact le_antisymm hsInf_le hn_le

section

variable [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.36: for a monotone `ℕ`-valued path started at `0`, prescribing all
adjacent increments is equivalent to prescribing all endpoint values by cumulative sums. -/
theorem nat_increment_event_iff_endpoint_counts
    {X k : ℕ → ℕ} (hX0 : X 0 = 0) (hXmono : Monotone X) :
    (∀ i, X (i + 1) - X i = k i) ↔ ∀ j, X j = ∑ i ∈ Finset.range j, k i := by
  constructor
  · intro hinc j
    induction j with
    | zero =>
        -- Proof comment: the zero-anchored endpoint is fixed by the initial condition.
        simpa using hX0
    | succ j ih =>
        have hstep : X (j + 1) = X j + k j := by
          have hle : X j ≤ X (j + 1) := hXmono (Nat.le_succ j)
          have hinc_j := hinc j
          omega
        -- Proof comment: add the next prescribed increment to the cumulative endpoint count.
        calc
          X (j + 1) = X j + k j := hstep
          _ = (∑ i ∈ Finset.range j, k i) + k j := by rw [ih]
          _ = ∑ i ∈ Finset.range (j + 1), k i := by
                rw [Finset.sum_range_succ]
  · intro hend i
    have hstep : X (i + 1) = X i + k i := by
      rw [hend (i + 1), hend i, Finset.sum_range_succ]
    -- Proof comment: subtract the previous endpoint from the successor identity.
    have hle : X i ≤ X (i + 1) := hXmono (Nat.le_succ i)
    have : X (i + 1) - X i = k i := by
      omega
    exact this

/-- Helper for Theorem 5.36: every coordinate of the i.i.d. interarrival sequence has the same
exponential law as the distinguished coordinate `W 0`. -/
theorem interarrival_hasLaw_of_iid_exponential
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ) (n : ℕ) :
    HasLaw (W n) (expMeasure α) μ := by
  -- Proof comment: identical distribution transports the exponential law from `W 0` to `W n`.
  exact (hW_iid.identDistrib 0 n).hasLaw hW0_law

/-- Helper for Theorem 5.36: every finite prefix of the i.i.d. interarrival sequence has the
finite product of exponential laws as its distribution. -/
theorem iid_exponential_prefix_hasLaw_pi
    (μ : Measure Ω) [IsProbabilityMeasure μ] (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ) (n : ℕ) :
    HasLaw (fun ω ↦ fun i : Fin n ↦ W i ω) (Measure.pi (fun _ : Fin n ↦ expMeasure α)) μ := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: the finite coordinate vector is almost everywhere measurable coordinatewise.
    exact aemeasurable_pi_lambda _ fun i : Fin n ↦
      (interarrival_hasLaw_of_iid_exponential μ α W hW_iid hW0_law i).aemeasurable
  · have h_prefix_iIndep : iIndepFun (fun i : Fin n ↦ W i) μ :=
      hW_iid.iIndepFun.precomp Fin.val_injective
    -- Proof comment: restrict the i.i.d. family to the finite index type `Fin n`.
    rw [(
      iIndepFun_iff_map_fun_eq_pi_map
        (fun i : Fin n ↦
          (interarrival_hasLaw_of_iid_exponential μ α W hW_iid hW0_law i).aemeasurable)).1
      h_prefix_iIndep]
    have h_marginals :
        (fun i : Fin n ↦ Measure.map (W i) μ) = fun _ : Fin n ↦ expMeasure α := by
      funext i
      exact (interarrival_hasLaw_of_iid_exponential μ α W hW_iid hW0_law i).map_eq
    -- Proof comment: each coordinate marginal is the same exponential law.
    rw [h_marginals]

/-- Helper for Theorem 5.36: every contiguous finite block of the i.i.d. interarrival sequence has
the corresponding finite product exponential law. -/
theorem iid_exponential_contiguous_block_hasLaw_pi
    (μ : Measure Ω) [IsProbabilityMeasure μ] (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ) (a n : ℕ) :
    HasLaw (fun ω ↦ fun i : Fin n ↦ W (a + i) ω)
      (Measure.pi (fun _ : Fin n ↦ expMeasure α)) μ := by
  have h_block_iIndep : iIndepFun (fun i : Fin n ↦ W (a + i)) μ :=
    hW_iid.iIndepFun.precomp (fun {i j} hij ↦ by
      apply Fin.ext
      exact Nat.add_left_cancel hij)
  refine ⟨?_, ?_⟩
  · -- Proof comment: the finite shifted block is almost everywhere measurable coordinatewise.
    exact aemeasurable_pi_lambda _ fun i : Fin n ↦
      (interarrival_hasLaw_of_iid_exponential μ α W hW_iid hW0_law (a + i)).aemeasurable
  · -- Proof comment: restrict the i.i.d. family to the injectively shifted coordinates `a + i`.
    rw [(
      iIndepFun_iff_map_fun_eq_pi_map
        (fun i : Fin n ↦
          (interarrival_hasLaw_of_iid_exponential μ α W hW_iid hW0_law (a + i)).aemeasurable)).1
      h_block_iIndep]
    have h_marginals :
        (fun i : Fin n ↦ Measure.map (W (a + i)) μ) = fun _ : Fin n ↦ expMeasure α := by
      funext i
      exact (interarrival_hasLaw_of_iid_exponential μ α W hW_iid hW0_law (a + i)).map_eq
    rw [h_marginals]

/-- Helper for Theorem 5.36: every interarrival is almost surely strictly positive under the
exponential-law hypothesis. -/
theorem ae_interarrival_pos_of_iid_exponential
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α) :
    ∀ᵐ ω ∂μ, ∀ n, 0 < W n ω := by
  have hα_real : 0 < (α : ℝ) := by
    exact_mod_cast hα
  have h_pos_exp : ∀ᵐ x ∂ expMeasure α, 0 < x := by
    -- Proof comment: the exponential distribution assigns zero mass to `(-∞, 0]`.
    have hIic_zero : expMeasure α (Set.Iic (0 : ℝ)) = 0 := by
      letI : IsProbabilityMeasure (expMeasure α) :=
        ProbabilityTheory.isProbabilityMeasure_expMeasure hα_real
      have h_cdf_zero :
          ENNReal.ofReal (cdf (expMeasure α) (0 : ℝ)) = expMeasure α (Set.Iic (0 : ℝ)) :=
        ofReal_cdf (expMeasure α) (0 : ℝ)
      rw [← h_cdf_zero]
      rw [ProbabilityTheory.cdf_expMeasure_eq hα_real 0]
      simp
    rw [ae_iff]
    simpa [not_lt] using hIic_zero
  refine ae_all_iff.2 fun n ↦ ?_
  have hWn_law :=
    interarrival_hasLaw_of_iid_exponential μ α W hW_iid hW0_law n
  -- Proof comment: transfer the positivity event through the law of `W n`.
  exact (hWn_law.ae_iff (measurable_const.lt measurable_id)).2 h_pos_exp

/-- Helper for Theorem 5.36: an i.i.d. exponential interarrival sequence almost surely has
strictly increasing arrival times and arrival times diverging to `∞`. -/
private theorem ae_arrivalTime_strictMono_and_tendsto_of_iid_exponential
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α) :
    ∀ᵐ ω ∂μ,
      StrictMono (fun n ↦ arrivalTime W n ω) ∧
        Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop := by
  let F : ℝ → ℝ := Set.indicator (Set.Ioi (1 : ℝ)) (fun _ ↦ (1 : ℝ))
  let Y : ℕ → Ω → ℝ := fun n ω ↦ F (W n ω)
  have hα_real : 0 < (α : ℝ) := by
    exact_mod_cast hα
  letI : IsProbabilityMeasure (expMeasure α) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hα_real
  have hF_meas : Measurable F := by
    -- Proof comment: the large-gap indicator is measurable because `Ioi 1` is measurable.
    simpa [F] using (measurable_indicator_const_iff (1 : ℝ)).2 measurableSet_Ioi
  have hF_law : HasLaw F ((expMeasure α).map F) (expMeasure α) := by
    exact
      (show MeasurePreserving F (expMeasure α) ((expMeasure α).map F) from
        ⟨hF_meas, rfl⟩).hasLaw
  have hF_integrable : Integrable F (expMeasure α) := by
    -- Proof comment: `F` is a bounded indicator, hence integrable under the probability law.
    simpa [F] using (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
  have hY_iIndep : iIndepFun Y μ := by
    -- Proof comment: independence is preserved under measurable postcomposition.
    simpa [Y] using hW_iid.iIndepFun.comp (fun _ ↦ F) (fun _ ↦ hF_meas)
  have hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ := by
    -- Proof comment: all large-gap indicators have the same law because the interarrivals are
    -- identically distributed.
    intro n
    simpa [Y] using (hW_iid.identDistrib n 0).comp hF_meas
  have hY0_ident : IdentDistrib (Y 0) F μ (expMeasure α) := by
    have hY0_law : HasLaw (Y 0) ((expMeasure α).map F) μ := by
      -- Proof comment: push the law of `W 0` forward through the indicator map `F`.
      simpa [Y] using hF_law.fun_comp hW0_law
    exact hY0_law.identDistrib hF_law
  have hY0_integrable : Integrable (Y 0) μ := by
    -- Proof comment: integrability transfers across identical distribution.
    exact hY0_ident.integrable_iff.2 hF_integrable
  have hY0_expectation : μ[Y 0] = (expMeasure α).real (Set.Ioi (1 : ℝ)) := by
    -- Proof comment: the mean of the indicator is exactly the tail probability above `1`.
    calc
      μ[Y 0] = ∫ x, F x ∂expMeasure α := by
        simpa [Y] using hW0_law.integral_comp hF_meas.aestronglyMeasurable
      _ = (expMeasure α).real (Set.Ioi (1 : ℝ)) := by
        simp [F, integral_indicator_const, measurableSet_Ioi, smul_eq_mul]
  have hIic_one : (expMeasure α).real (Set.Iic (1 : ℝ)) = 1 - Real.exp (-(α : ℝ)) := by
    -- Proof comment: evaluate the exponential cdf at the threshold `1`.
    letI : IsProbabilityMeasure (expMeasure α) :=
      ProbabilityTheory.isProbabilityMeasure_expMeasure hα_real
    have h_cdf_one :
        cdf (expMeasure α) (1 : ℝ) = (expMeasure α).real (Set.Iic (1 : ℝ)) :=
      cdf_eq_real (expMeasure α) (1 : ℝ)
    rw [← h_cdf_one]
    rw [ProbabilityTheory.cdf_expMeasure_eq hα_real 1]
    simp
  have hIoi_one : (expMeasure α).real (Set.Ioi (1 : ℝ)) = Real.exp (-(α : ℝ)) := by
    -- Proof comment: the tail probability is the complement of the cdf value at `1`.
    letI : IsProbabilityMeasure (expMeasure α) :=
      ProbabilityTheory.isProbabilityMeasure_expMeasure hα_real
    calc
      (expMeasure α).real (Set.Ioi (1 : ℝ))
          = 1 - (expMeasure α).real (Set.Iic (1 : ℝ)) := by
              simpa using
                (show (expMeasure α).real (Set.Iic (1 : ℝ))ᶜ =
                    1 - (expMeasure α).real (Set.Iic (1 : ℝ)) from
                  probReal_compl_eq_one_sub measurableSet_Iic)
      _ = Real.exp (-(α : ℝ)) := by
        rw [hIic_one]
        ring
  have hY0_expectation_pos : 0 < μ[Y 0] := by
    -- Proof comment: the exponential law has positive mass on the tail `(1, ∞)`.
    rw [hY0_expectation, hIoi_one]
    exact Real.exp_pos _
  have hY_limit :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, Y i ω) / n) atTop
        (𝓝 (μ[Y 0])) := by
    -- Proof comment: apply the strong law to the i.i.d. large-gap indicators.
    exact ProbabilityTheory.strong_law_ae_real Y hY0_integrable
      (fun i j hij ↦ hY_iIndep.indepFun hij) hY_ident
  have hW_pos : ∀ᵐ ω ∂μ, ∀ n, 0 < W n ω :=
    ae_interarrival_pos_of_iid_exponential μ α W hW_iid hW0_law hα
  filter_upwards [hW_pos, hY_limit] with ω hW_pos_ω hY_limit_ω
  refine ⟨?_, ?_⟩
  · -- Proof comment: strictly positive interarrivals force strict growth of the arrival times.
    refine strictMono_nat_of_lt_succ fun n ↦ ?_
    rw [arrivalTime_succ]
    exact lt_add_of_pos_right _ (hW_pos_ω n)
  · -- Route correction: instead of estimating the raw exponential sums directly, we compare them
    -- with the count of interarrivals larger than `1`, whose strong-law limit is a positive
    -- constant. This yields a linear lower bound on the arrival times and hence divergence to `∞`.
    have hYsum_le_arrival : ∀ n, (∑ i ∈ Finset.range n, Y i ω) ≤ arrivalTime W n ω := by
      -- Proof comment: each indicator contribution is bounded by the corresponding interarrival.
      intro n
      calc
        ∑ i ∈ Finset.range n, Y i ω ≤ ∑ i ∈ Finset.range n, W i ω := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          by_cases hlarge : 1 < W i ω
          · simp [Y, F, hlarge]
            exact le_of_lt hlarge
          · have hnonneg : 0 ≤ W i ω := (hW_pos_ω i).le
            simp [Y, F, hlarge, hnonneg]
        _ = arrivalTime W n ω := by
          simp [arrivalTime]
    have hhalf_pos : 0 < μ[Y 0] / 2 := by
      linarith
    have hhalf_lt : μ[Y 0] / 2 < μ[Y 0] := by
      linarith
    have havg_eventually :
        ∀ᶠ n : ℕ in atTop, μ[Y 0] / 2 < (∑ i ∈ Finset.range n, Y i ω) / n := by
      -- Proof comment: the strong-law limit is positive, so the empirical frequency is
      -- eventually bounded below by half of that limit.
      exact hY_limit_ω.eventually (Ioi_mem_nhds hhalf_lt)
    have hlinear_le_sumY :
        (fun n : ℕ ↦ (μ[Y 0] / 2) * (n : ℝ)) ≤ᶠ[atTop] fun n ↦ ∑ i ∈ Finset.range n, Y i ω := by
      -- Proof comment: multiply the eventual lower bound on the empirical frequencies by `n`.
      filter_upwards [havg_eventually] with n hn
      by_cases hzero : n = 0
      · subst hzero
        simp
      · have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero)
        exact le_of_lt ((lt_div_iff₀ hn_pos).mp hn)
    have hlinear_tendsto :
        Tendsto (fun n : ℕ ↦ (μ[Y 0] / 2) * (n : ℝ)) atTop atTop := by
      -- Proof comment: a positive multiple of `n` still tends to `∞`.
      exact Filter.Tendsto.const_mul_atTop' hhalf_pos tendsto_natCast_atTop_atTop
    have harrival_lower :
        (fun n : ℕ ↦ (μ[Y 0] / 2) * (n : ℝ)) ≤ᶠ[atTop] fun n ↦ arrivalTime W n ω := by
      exact hlinear_le_sumY.trans (Filter.Eventually.of_forall hYsum_le_arrival)
    -- Proof comment: eventual domination by a divergent linear function forces the arrival times
    -- themselves to diverge to `∞`.
    exact tendsto_atTop_mono' atTop harrival_lower hlinear_tendsto

/-- Helper for Theorem 5.36: an i.i.d. exponential interarrival sequence almost surely has
strictly increasing arrival times. -/
theorem ae_arrivalTime_strictMono_of_iid_exponential
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α) :
    ∀ᵐ ω ∂μ, StrictMono (fun n ↦ arrivalTime W n ω) := by
  filter_upwards
    [ae_arrivalTime_strictMono_and_tendsto_of_iid_exponential μ α W hW_iid hW0_law hα]
    with ω hω
  exact hω.1

/-- Helper for Theorem 5.36: an i.i.d. exponential interarrival sequence almost surely has arrival
times diverging to `∞`. -/
theorem ae_arrivalTime_tendsto_of_iid_exponential
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop := by
  filter_upwards
    [ae_arrivalTime_strictMono_and_tendsto_of_iid_exponential μ α W hW_iid hW0_law hα]
    with ω hω
  exact hω.2

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.36: along a zero-anchored monotone time grid on a genuine renewal path,
prescribing the increment vector is equivalent to prescribing the endpoint counts by cumulative
sums. -/
theorem renewal_increment_event_iff_endpoint_counts_zero_anchored
    (W : ℕ → Ω → ℝ) {ω : Ω}
    (h_arrival_strict : StrictMono (fun n ↦ arrivalTime W n ω))
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop)
    {u : ℕ → NNReal} (hu0 : u 0 = 0) (hu : Monotone u) (k : ℕ → ℕ) :
    (∀ i, renewalCountingProcess W (u (i + 1)) ω - renewalCountingProcess W (u i) ω = k i) ↔
      ∀ j, renewalCountingProcess W (u j) ω = ∑ i ∈ Finset.range j, k i := by
  -- Proof comment: first show the count process is monotone on the chosen grid, then telescope the
  -- endpoint values exactly as for an arbitrary monotone `ℕ`-valued path.
  let X : ℕ → ℕ := fun j ↦ renewalCountingProcess W (u j) ω
  have hX0 : X 0 = 0 := by
    have h_first_arrival : 0 < arrivalTime W 1 ω := by
      simpa [arrivalTime_zero] using h_arrival_strict (by simp : 0 < 1)
    simpa [X, hu0] using renewalCountingProcess_zero W ω h_first_arrival
  have hXmono : Monotone X := by
    simpa [X] using (renewalCountingProcess_mono W h_arrival_tendsto).comp hu
  simpa only [X] using
    (nat_increment_event_iff_endpoint_counts hX0 hXmono :
      (∀ i, X (i + 1) - X i = k i) ↔ ∀ j, X j = ∑ i ∈ Finset.range j, k i)

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.36: along a genuine renewal path, endpoint counts are equivalent to the
corresponding arrival-time strip conditions. -/
theorem renewal_endpoint_counts_iff_arrival_strips
    (W : ℕ → Ω → ℝ) {ω : Ω}
    (h_arrival_strict : StrictMono (fun n ↦ arrivalTime W n ω))
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop)
    (u : ℕ → NNReal) (K : ℕ → ℕ) :
    (∀ j, renewalCountingProcess W (u j) ω = K j) ↔
      ∀ j, arrivalTime W (K j) ω ≤ u j ∧ u j < arrivalTime W (K j + 1) ω := by
  constructor
  · intro hK j
    -- Proof comment: rewrite each endpoint count through the pathwise strip characterization.
    have hspec :
        arrivalTime W (renewalCountingProcess W (u j) ω) ω ≤ u j ∧
          u j < arrivalTime W (renewalCountingProcess W (u j) ω + 1) ω :=
      renewalCountingProcess_spec W h_arrival_tendsto
    rw [hK j] at hspec
    exact hspec
  · intro hstrip j
    -- Proof comment: the strip inequalities determine the count uniquely on a genuine renewal path.
    exact
      (renewalCountingProcess_eq_iff_arrival_strip W h_arrival_strict h_arrival_tendsto).2
        (hstrip j)

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.36: on a genuine renewal path, fixing the count at time `s` and the
increment over `[s,t]` is equivalent to prescribing the two textbook arrival strips at `s` and
`t`. -/
theorem renewal_increment_two_time_iff_arrival_strips
    (W : ℕ → Ω → ℝ) {ω : Ω}
    (h_arrival_strict : StrictMono (fun n ↦ arrivalTime W n ω))
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop)
    {s t : NNReal} (hst : s ≤ t) {k l : ℕ} :
    (renewalCountingProcess W s ω = k ∧
        renewalCountingProcess W t ω - renewalCountingProcess W s ω = l) ↔
      (arrivalTime W k ω ≤ s ∧
        s < arrivalTime W (k + 1) ω ∧
        arrivalTime W (k + l) ω ≤ t ∧
        t < arrivalTime W (k + l + 1) ω) := by
  constructor
  · rintro ⟨hs_count, hinc⟩
    have hcount_le :
        renewalCountingProcess W s ω ≤ renewalCountingProcess W t ω :=
      (renewalCountingProcess_mono W h_arrival_tendsto) hst
    have ht_count : renewalCountingProcess W t ω = k + l := by
      omega
    have hs_strip :=
      (renewalCountingProcess_eq_iff_arrival_strip W h_arrival_strict h_arrival_tendsto).1 hs_count
    have ht_strip :=
      (renewalCountingProcess_eq_iff_arrival_strip W h_arrival_strict h_arrival_tendsto).1
        ht_count
    -- Proof comment: the increment identity upgrades the endpoint count at time `t` from `N s = k`
    -- to `N t = k + l`, so both times are described by the usual arrival strips.
    exact ⟨hs_strip.1, hs_strip.2, ht_strip.1, ht_strip.2⟩
  · rintro ⟨hs_lower, hs_upper, ht_lower, ht_upper⟩
    have hs_count :
        renewalCountingProcess W s ω = k :=
      (renewalCountingProcess_eq_iff_arrival_strip W h_arrival_strict h_arrival_tendsto).2
        ⟨hs_lower, hs_upper⟩
    have ht_count :
        renewalCountingProcess W t ω = k + l :=
      (renewalCountingProcess_eq_iff_arrival_strip W h_arrival_strict h_arrival_tendsto).2
        ⟨ht_lower, ht_upper⟩
    -- Proof comment: once the endpoint counts are fixed to `k` and `k + l`, the increment is
    -- exactly `l` by arithmetic on natural numbers.
    refine ⟨hs_count, ?_⟩
    rw [ht_count, hs_count]
    exact Nat.add_sub_cancel_left k l

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.36: after fixing the count `N_s = k`, the increment over `[s,t]` is
equivalent to a strip condition for the contiguous block of interarrivals starting at `k`,
measured relative to the `k`th arrival time `T_k`. This is the correct block rewrite for the
textbook event; the threshold is `(t - T_k)`, not merely `(t - s)`. -/
theorem renewal_increment_two_time_iff_relative_block_strip
    (W : ℕ → Ω → ℝ) {ω : Ω}
    (h_arrival_strict : StrictMono (fun n ↦ arrivalTime W n ω))
    (h_arrival_tendsto : Tendsto (fun n ↦ arrivalTime W n ω) atTop atTop)
    {s t : NNReal} (hst : s ≤ t) {k l : ℕ} :
    (renewalCountingProcess W s ω = k ∧
        renewalCountingProcess W t ω - renewalCountingProcess W s ω = l) ↔
      (arrivalTime W k ω ≤ s ∧
        s < arrivalTime W (k + 1) ω ∧
        (∑ i ∈ Finset.range l, W (k + i) ω) ≤ (t : ℝ) - arrivalTime W k ω ∧
        (t : ℝ) - arrivalTime W k ω <
          ∑ i ∈ Finset.range (l + 1), W (k + i) ω) := by
  constructor
  · intro hcount
    rcases (renewal_increment_two_time_iff_arrival_strips
      W h_arrival_strict h_arrival_tendsto hst).1 hcount with
      ⟨hs_lower, hs_upper, ht_lower, ht_upper⟩
    have hkl :
        arrivalTime W (k + l) ω =
          arrivalTime W k ω + ∑ i ∈ Finset.range l, W (k + i) ω :=
      arrivalTime_add W k l ω
    have hkl1 :
        arrivalTime W (k + l + 1) ω =
          arrivalTime W k ω + ∑ i ∈ Finset.range (l + 1), W (k + i) ω := by
      simpa [Nat.add_assoc] using arrivalTime_add W k (l + 1) ω
    refine ⟨hs_lower, hs_upper, ?_, ?_⟩
    · -- Proof comment: rewrite `T_(k+l)` by splitting off the first `k` interarrivals.
      rw [hkl] at ht_lower
      linarith
    · -- Proof comment: do the same for `T_(k+l+1)` to obtain the upper strip inequality.
      rw [hkl1] at ht_upper
      linarith
  · rintro ⟨hs_lower, hs_upper, ht_lower, ht_upper⟩
    have hkl :
        arrivalTime W (k + l) ω =
          arrivalTime W k ω + ∑ i ∈ Finset.range l, W (k + i) ω :=
      arrivalTime_add W k l ω
    have hkl1 :
        arrivalTime W (k + l + 1) ω =
          arrivalTime W k ω + ∑ i ∈ Finset.range (l + 1), W (k + i) ω := by
      simpa [Nat.add_assoc] using arrivalTime_add W k (l + 1) ω
    have ht_lower' : arrivalTime W (k + l) ω ≤ t := by
      -- Proof comment: move the relative lower bound back to the absolute arrival time scale.
      rw [hkl]
      linarith
    have ht_upper' : t < arrivalTime W (k + l + 1) ω := by
      -- Proof comment: the relative upper bound is exactly the strict strip condition at time `t`.
      rw [hkl1]
      linarith
    exact (renewal_increment_two_time_iff_arrival_strips
      W h_arrival_strict h_arrival_tendsto hst).2
      ⟨hs_lower, hs_upper, ht_lower', ht_upper'⟩

-- Proof sketch: use Definition 5.33. The pathwise bookkeeping for the `sInf`-based counting rule
-- is isolated in the public pathwise specification lemma above, while the public theorem
-- states only the distributional content of the textbook result. Independent increments come from
-- disjoint blocks of the i.i.d. interarrival sequence `W`, and the single-coordinate exponential
-- law propagates to every coordinate via `IsIID`; Theorem 5.35 then identifies each increment
-- over `[s,t]` with a Poisson law of parameter `α * (t - s)`.
/-- Theorem 5.36: if the interarrival sequence is i.i.d. in the chapter's canonical sense and one
coordinate has exponential law of rate `α`, then the textbook renewal counting process associated
with `W` is a Poisson process with intensity `α`. On the almost-sure set of genuine renewal paths,
the companion lemmas above identify it with the usual arrival-strip characterization. -/
theorem renewalCountingProcess_isPoissonProcess_of_iid_exponential_interarrivals
    (μ : Measure Ω) (α : NNReal) (W : ℕ → Ω → ℝ)
    (hW_iid : IsIID W μ)
    (hW0_law : HasLaw (W 0) (expMeasure α) μ)
    (hα : 0 < α) :
    IsPoissonProcess α μ (renewalCountingProcess W) := by
  -- The remaining proof must verify the owner fields directly for the raw `sInf`-counting rule.
  refine isPoissonProcess_of_textbook ?_ ?_ ?_ ?_ ?_
  · sorry
  · sorry
  · sorry
  · -- TODO: prove independent increments by identifying each increment with a disjoint block of
    -- exponential interarrivals on the almost-sure renewal-path event and then packaging the
    -- resulting finite-dimensional factorization into `HasIndepIncrements`.
    -- Route correction: the pathwise bridge is now split into
    -- `renewal_increment_event_iff_endpoint_counts_zero_anchored` and
    -- `renewal_endpoint_counts_iff_arrival_strips`; the remaining blocker is the strict-grid
    -- singleton-mass computation for the arrival-strip event.
    sorry
  · intro s t hst
    -- TODO: prove the strict increment law by the textbook density computation for exponential
    -- interarrivals, yielding the Poisson law with parameter `α * (t - s)`.
    -- Route correction: after the new pointwise strip equivalence, the remaining work is to
    -- evaluate the two-time strip probability and compare singleton masses with
    -- `poissonMeasure (α * (t - s))`.
    sorry

end
