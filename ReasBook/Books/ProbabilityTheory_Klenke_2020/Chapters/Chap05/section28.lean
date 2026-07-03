import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_5_28 (from Items/Chap05) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- The coordinate process on the path space `ℝ^ℕ`. -/
def coordinateProcess (n : ℕ) : (ℕ → ℝ) → ℝ :=
  fun ω ↦ ω n

/-- The partial sum `Sₙ = X₀ + ⋯ + Xₙ₋₁` of a `0`-based real sequence `X 0, X 1, …`. For the
textbook indexing `X₁, X₂, …`, apply this definition to `fun k ↦ X (k + 1)`. -/
def partialSum (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range n, X i ω

-- Proof sketch: unfold `partialSum`; it is exactly the finite sum over `Finset.range n`.
/-- The partial sum evaluates pointwise as the sum of the first `n` terms. -/
theorem partialSum_apply (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    partialSum X n ω = ∑ i ∈ Finset.range n, X i ω := by
  -- This is exactly the defining finite sum.
  rfl

-- Proof sketch: rewrite the shifted `0`-based sum over `Finset.range n` as the textbook sum over
-- `Finset.Icc 1 n`.
/-- For the textbook sequence `X₁, X₂, …`, represented by `fun k ↦ X (k + 1)`, the partial sum is
`Sₙ = X₁ + ⋯ + Xₙ`. -/
theorem partialSum_textbook_apply (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    partialSum (fun k ↦ X (k + 1)) n ω = ∑ i ∈ Finset.Icc 1 n, X i ω := by
  -- Reindex the shifted range sum as the interval `Icc 1 n`.
  rw [partialSum]
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

/-- Helper for Theorem 5.28: the event that one of the first `n` partial sums reaches `t`. -/
def oneSidedHitEvent (X : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) : Set Ω :=
  {ω | ∃ k ∈ Finset.Icc 1 n, t ≤ partialSum X k ω}

/-- Helper for Theorem 5.28: the event that `k` is the first partial-sum index reaching `t`. -/
private def firstHitEvent (X : ℕ → Ω → ℝ) (t : ℝ) (k : ℕ) : Set Ω :=
  {ω | (∀ j ∈ Finset.Icc 1 (k - 1), partialSum X j ω < t) ∧ t ≤ partialSum X k ω}

/-- Helper for Theorem 5.28: the event that one of the first `n` partial sums has absolute value
at least `t`. -/
def absHitEvent (X : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) : Set Ω :=
  {ω | ∃ k ∈ Finset.Icc 1 n, t ≤ |partialSum X k ω|}

/-- Helper for Theorem 5.28: the event that `k` is the first index whose partial sum has absolute
value at least `t`. -/
private def absFirstHitEvent (X : ℕ → Ω → ℝ) (t : ℝ) (k : ℕ) : Set Ω :=
  {ω | (∀ j ∈ Finset.Icc 1 (k - 1), |partialSum X j ω| < t) ∧ t ≤ |partialSum X k ω|}

/-- Helper for Theorem 5.28: every shorter partial sum is still centered. -/
private lemma partialSum_mean_zero (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    {n k : ℕ}
    (hk : k ≤ n) (hX_mean : ∀ i ∈ Finset.range n, P[X i] = 0)
    (hX_memLp : ∀ i ∈ Finset.range n, MemLp (X i) 2 P) :
    P[partialSum X k] = 0 := by
  -- Restrict the hypotheses from `range n` to `range k`.
  have h_mean : ∀ i ∈ Finset.range k, P[X i] = 0 := by
    intro i hi
    exact hX_mean i <| Finset.mem_range.mpr <| lt_of_lt_of_le (Finset.mem_range.mp hi) hk
  have h_int : ∀ i ∈ Finset.range k, Integrable (X i) P := by
    intro i hi
    exact
      (hX_memLp i <| Finset.mem_range.mpr <| lt_of_lt_of_le (Finset.mem_range.mp hi) hk).integrable
        (by norm_num)
  -- Expand the expectation of the finite sum and use the centered summands.
  change ∫ ω, (∑ i ∈ Finset.range k, X i ω) ∂P = 0
  rw [integral_finset_sum]
  · rw [Finset.sum_eq_zero]
    intro i hi
    exact h_mean i hi
  · intro i hi
    exact h_int i hi

/-- Helper for Theorem 5.28: each initial partial sum stays in `L²` once the first `n` summands
are in `L²`. -/
private lemma partialSum_memLp_two (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    {n k : ℕ}
    (hk : k ≤ n) (hX_memLp : ∀ i ∈ Finset.range n, MemLp (X i) 2 P) :
    MemLp (partialSum X k) 2 P := by
  -- Restrict the `L²` hypotheses from `range n` to the shorter prefix `range k`.
  rw [show partialSum X k = (fun ω ↦ ∑ i ∈ Finset.range k, X i ω) by rfl]
  refine memLp_finset_sum (Finset.range k) ?_
  intro i hi
  exact hX_memLp i <| Finset.mem_range.mpr <| lt_of_lt_of_le (Finset.mem_range.mp hi) hk

/-- Helper for Theorem 5.28: the tail increment from `k` to `n` is the corresponding `Ico` sum. -/
lemma partialSum_sub_eq_sum_Ico (X : ℕ → Ω → ℝ) {k n : ℕ} (hk : k ≤ n) (ω : Ω) :
    partialSum X n ω - partialSum X k ω = ∑ i ∈ Finset.Ico k n, X i ω := by
  -- Split the long partial sum into the prefix up to `k` and the future block `Ico k n`.
  rw [partialSum_apply, partialSum_apply]
  have hsplit :
      ∑ i ∈ Finset.range n, X i ω =
        ∑ i ∈ Finset.range k, X i ω + ∑ i ∈ Finset.Ico k n, X i ω := by
    simpa using (Finset.sum_range_add_sum_Ico (fun i ↦ X i ω) hk).symm
  have hdiff := congrArg (fun x : ℝ ↦ x - ∑ i ∈ Finset.range k, X i ω) hsplit
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdiff

/-- Helper for Theorem 5.28: two different first-hit layers cannot occur simultaneously. -/
private lemma firstHitEvent_disjoint (X : ℕ → Ω → ℝ) {n k l : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (hl : l ∈ Finset.Icc 1 n) (hkl : k ≠ l) (t : ℝ) :
    Disjoint (firstHitEvent X t k) (firstHitEvent X t l) := by
  rw [Set.disjoint_iff]
  intro ω hω
  rcases hω with ⟨hkω, hlω⟩
  rcases hkω with ⟨hkprev, hkge⟩
  rcases hlω with ⟨hlprev, hlge⟩
  rcases lt_or_gt_of_ne hkl with hlt | hlt
  · -- The later first-hit condition forces the earlier partial sum to stay below `t`.
    have hkIcc := Finset.mem_Icc.mp hk
    have hk_mem : k ∈ Finset.Icc 1 (l - 1) := by
      exact Finset.mem_Icc.mpr ⟨hkIcc.1, Nat.le_pred_of_lt hlt⟩
    exact not_lt_of_ge hkge (hlprev k hk_mem)
  · -- Swapping the roles of `k` and `l` gives the symmetric contradiction.
    have hlIcc := Finset.mem_Icc.mp hl
    have hl_mem : l ∈ Finset.Icc 1 (k - 1) := by
      exact Finset.mem_Icc.mpr ⟨hlIcc.1, Nat.le_pred_of_lt hlt⟩
    exact not_lt_of_ge hlge (hkprev l hl_mem)

/-- Helper for Theorem 5.28: every hit belongs to its least hitting layer. -/
private lemma exists_firstHitEvent (X : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω)
    (hω : ω ∈ oneSidedHitEvent X n t) :
    ∃ k ∈ Finset.Icc 1 n, ω ∈ firstHitEvent X t k := by
  let p : ℕ → Prop := fun k ↦ k ∈ Finset.Icc 1 n ∧ t ≤ partialSum X k ω
  have hp : ∃ k, p k := hω
  refine ⟨Nat.find hp, (Nat.find_spec hp).1, ?_⟩
  refine ⟨?_, (Nat.find_spec hp).2⟩
  intro j hj
  by_contra hjge
  have hjIcc := Finset.mem_Icc.mp hj
  have hfindIcc := Finset.mem_Icc.mp (Nat.find_spec hp).1
  have hj_mem : j ∈ Finset.Icc 1 n := by
    refine Finset.mem_Icc.mpr ⟨hjIcc.1, le_of_lt ?_⟩
    calc
      j ≤ Nat.find hp - 1 := hjIcc.2
      _ < Nat.find hp := Nat.sub_lt (by linarith) (by omega)
      _ ≤ n := hfindIcc.2
  have hj_lt_find : j < Nat.find hp := by
    calc
      j ≤ Nat.find hp - 1 := hjIcc.2
      _ < Nat.find hp := Nat.sub_lt (by linarith) (by omega)
  exact (Nat.find_min hp hj_lt_find) ⟨hj_mem, not_lt.mp hjge⟩

/-- Helper for Theorem 5.28: two different absolute first-hit layers are disjoint. -/
private lemma absFirstHitEvent_disjoint (X : ℕ → Ω → ℝ) {n k l : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (hl : l ∈ Finset.Icc 1 n) (hkl : k ≠ l) (t : ℝ) :
    Disjoint (absFirstHitEvent X t k) (absFirstHitEvent X t l) := by
  rw [Set.disjoint_iff]
  intro ω hω
  rcases hω with ⟨hkω, hlω⟩
  rcases hkω with ⟨hkprev, hkge⟩
  rcases hlω with ⟨hlprev, hlge⟩
  rcases lt_or_gt_of_ne hkl with hlt | hlt
  · -- The later absolute first-hit condition forces the earlier absolute value below `t`.
    have hkIcc := Finset.mem_Icc.mp hk
    have hk_mem : k ∈ Finset.Icc 1 (l - 1) := by
      exact Finset.mem_Icc.mpr ⟨hkIcc.1, Nat.le_pred_of_lt hlt⟩
    exact not_lt_of_ge hkge (hlprev k hk_mem)
  · -- Swapping the roles of `k` and `l` gives the symmetric contradiction.
    have hlIcc := Finset.mem_Icc.mp hl
    have hl_mem : l ∈ Finset.Icc 1 (k - 1) := by
      exact Finset.mem_Icc.mpr ⟨hlIcc.1, Nat.le_pred_of_lt hlt⟩
    exact not_lt_of_ge hlge (hkprev l hl_mem)

/-- Helper for Theorem 5.28: every absolute hit belongs to its least absolute first-hit layer. -/
private lemma exists_absFirstHitEvent (X : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω)
    (hω : ω ∈ absHitEvent X n t) :
    ∃ k ∈ Finset.Icc 1 n, ω ∈ absFirstHitEvent X t k := by
  let p : ℕ → Prop := fun k ↦ k ∈ Finset.Icc 1 n ∧ t ≤ |partialSum X k ω|
  have hp : ∃ k, p k := hω
  refine ⟨Nat.find hp, (Nat.find_spec hp).1, ?_⟩
  refine ⟨?_, (Nat.find_spec hp).2⟩
  intro j hj
  by_contra hjge
  have hjIcc := Finset.mem_Icc.mp hj
  have hfindIcc := Finset.mem_Icc.mp (Nat.find_spec hp).1
  have hj_mem : j ∈ Finset.Icc 1 n := by
    refine Finset.mem_Icc.mpr ⟨hjIcc.1, le_of_lt ?_⟩
    calc
      j ≤ Nat.find hp - 1 := hjIcc.2
      _ < Nat.find hp := Nat.sub_lt (by linarith) (by omega)
      _ ≤ n := hfindIcc.2
  have hj_lt_find : j < Nat.find hp := by
    calc
      j ≤ Nat.find hp - 1 := hjIcc.2
      _ < Nat.find hp := Nat.sub_lt (by linarith) (by omega)
  exact (Nat.find_min hp hj_lt_find) ⟨hj_mem, not_lt.mp hjge⟩

/-- Helper for Theorem 5.28: the tuple-level prefix sum cut off at `j` inside a `k`-tuple. -/
private def prefixVec (k : ℕ) (z : Fin k → ℝ) (j : ℕ) : ℝ :=
  ∑ i : Fin k, (if (i : ℕ) < j then z i else 0)

-- Proof sketch: convert the `Fin k` sum to a sum over `range k`, then split that range at `j`.
/-- Helper for Theorem 5.28: evaluating the tuple-level prefix sum on the first `k` coordinates
recovers the original partial sum up to any `j ≤ k`. -/
private lemma prefixVec_eq_partialSum (X : ℕ → Ω → ℝ) {j k : ℕ} (hj : j ≤ k) (ω : Ω) :
    prefixVec k (fun i : Fin k ↦ X i ω) j = partialSum X j ω := by
  -- Convert the finite tuple sum to the textbook `range` sum and then drop the zero tail.
  rw [prefixVec]
  calc
    ∑ i : Fin k, (if (i : ℕ) < j then X i ω else 0)
      = ∑ i ∈ Finset.range k, (if i < j then X i ω else 0) := by
          simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ if i < j then X i ω else 0) k)
    _ = ∑ i ∈ Finset.range (j + (k - j)), (if i < j then X i ω else 0) := by
          simp [Nat.add_sub_of_le hj]
    _ = ∑ i ∈ Finset.range j, X i ω
          + ∑ i ∈ Finset.range (k - j), (if j + i < j then X (j + i) ω else 0) := by
          rw [Finset.sum_range_add]
          refine congrArg (fun x : ℝ ↦ x + _) ?_
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [Finset.mem_range.mp hi]
    _ = ∑ i ∈ Finset.range j, X i ω := by
          simp
    _ = partialSum X j ω := by
          rw [partialSum]

/-- Helper for Theorem 5.28: tuple-level prefix sums are measurable on the finite product space. -/
private lemma measurable_prefixVec (k j : ℕ) :
    Measurable (fun z : Fin k → ℝ ↦ prefixVec k z j) := by
  -- Unfold the finite sum and use measurability of each coordinate projection.
  unfold prefixVec
  refine Finset.measurable_sum Finset.univ ?_
  intro i hi
  by_cases hij : (i : ℕ) < j
  · simpa [hij] using measurable_pi_apply i
  · simp [hij]

/-- Helper for Theorem 5.28: the tuple-space first-hit event for the one-sided threshold `t`. -/
private def firstHitPrefixSet (k : ℕ) (t : ℝ) : Set (Fin k → ℝ) :=
  (⋂ j ∈ Finset.Icc 1 (k - 1), {z | prefixVec k z j < t}) ∩ {z | t ≤ prefixVec k z k}

/-- Helper for Theorem 5.28: the tuple-space one-sided first-hit payload. -/
private def firstHitPrefixPayload (k : ℕ) (t c : ℝ) : (Fin k → ℝ) → ℝ :=
  Set.indicator (firstHitPrefixSet k t) (fun z ↦ prefixVec k z k + c)

/-- Helper for Theorem 5.28: the tuple-space first-hit event for the absolute threshold `t`. -/
private def absFirstHitPrefixSet (k : ℕ) (t : ℝ) : Set (Fin k → ℝ) :=
  (⋂ j ∈ Finset.Icc 1 (k - 1), {z | |prefixVec k z j| < t}) ∩ {z | t ≤ |prefixVec k z k|}

/-- Helper for Theorem 5.28: the tuple-space absolute first-hit payload. -/
private def absFirstHitPrefixPayload (k : ℕ) (t : ℝ) : (Fin k → ℝ) → ℝ :=
  Set.indicator (absFirstHitPrefixSet k t) (fun z ↦ prefixVec k z k)

/-- Helper for Theorem 5.28: the one-sided tuple-space first-hit set is measurable. -/
private lemma measurableSet_firstHitPrefixSet (k : ℕ) (t : ℝ) :
    MeasurableSet (firstHitPrefixSet k t) := by
  -- The first-hit condition is a finite intersection of measurable threshold sets.
  have hprev :
      MeasurableSet (⋂ j ∈ Finset.Icc 1 (k - 1), {z : Fin k → ℝ | prefixVec k z j < t}) := by
    refine Finset.measurableSet_biInter (Finset.Icc 1 (k - 1)) fun j _ ↦ ?_
    exact measurableSet_lt (measurable_prefixVec k j) measurable_const
  have hlast : MeasurableSet {z : Fin k → ℝ | t ≤ prefixVec k z k} :=
    measurableSet_le measurable_const (measurable_prefixVec k k)
  simpa [firstHitPrefixSet] using hprev.inter hlast

/-- Helper for Theorem 5.28: the absolute tuple-space first-hit set is measurable. -/
private lemma measurableSet_absFirstHitPrefixSet (k : ℕ) (t : ℝ) :
    MeasurableSet (absFirstHitPrefixSet k t) := by
  -- The absolute-value first-hit condition is also a finite intersection of measurable thresholds.
  have hprev :
      MeasurableSet (⋂ j ∈ Finset.Icc 1 (k - 1), {z : Fin k → ℝ | |prefixVec k z j| < t}) := by
    refine Finset.measurableSet_biInter (Finset.Icc 1 (k - 1)) fun j _ ↦ ?_
    exact measurableSet_lt ((measurable_prefixVec k j).abs) measurable_const
  have hlast : MeasurableSet {z : Fin k → ℝ | t ≤ |prefixVec k z k|} :=
    measurableSet_le measurable_const ((measurable_prefixVec k k).abs)
  simpa [absFirstHitPrefixSet] using hprev.inter hlast

/-- Helper for Theorem 5.28: the tuple-space one-sided payload is measurable. -/
private lemma measurable_firstHitPrefixPayload (k : ℕ) (t c : ℝ) :
    Measurable (firstHitPrefixPayload k t c) := by
  -- Once the first-hit set is measurable, the indicator of the measurable payload stays measurable.
  exact Measurable.indicator ((measurable_prefixVec k k).add_const c)
    (measurableSet_firstHitPrefixSet k t)

/-- Helper for Theorem 5.28: the tuple-space absolute payload is measurable. -/
private lemma measurable_absFirstHitPrefixPayload (k : ℕ) (t : ℝ) :
    Measurable (absFirstHitPrefixPayload k t) := by
  -- The same indicator measurability argument works for the absolute-value payload.
  exact Measurable.indicator (measurable_prefixVec k k)
    (measurableSet_absFirstHitPrefixSet k t)

/-- Helper for Theorem 5.28: the concrete one-sided first-hit payload factors through the first `k`
coordinates. -/
private lemma first_hit_payload_comp (X : ℕ → Ω → ℝ) {k : ℕ} (_hk : 1 ≤ k) (t c : ℝ) (ω : Ω) :
    firstHitPrefixPayload k t c (fun i : Fin k ↦ X i ω) =
      Set.indicator (firstHitEvent X t k) (fun ω ↦ partialSum X k ω + c) ω := by
  -- Evaluate the tuple payload on the concrete prefix coordinates and rewrite each prefix sum.
  classical
  have hmem :
      (fun i : Fin k ↦ X i ω) ∈ firstHitPrefixSet k t ↔ ω ∈ firstHitEvent X t k := by
    constructor
    · intro hz
      refine ⟨?_, ?_⟩
      · intro j hj
        have hj' := Finset.mem_Icc.mp hj
        have hzj := Set.mem_iInter.1 (Set.mem_iInter.1 hz.1 j) hj
        simpa [prefixVec_eq_partialSum X (le_trans hj'.2 (Nat.sub_le _ _)) ω] using hzj
      · simpa [firstHitPrefixSet, prefixVec_eq_partialSum X (show k ≤ k by rfl) ω] using hz.2
    · intro hω
      rcases hω with ⟨hprev, hkge⟩
      refine ⟨?_, ?_⟩
      · refine Set.mem_iInter.2 fun j ↦ Set.mem_iInter.2 fun hj ↦ ?_
        have hj' := Finset.mem_Icc.mp hj
        simpa [prefixVec_eq_partialSum X (le_trans hj'.2 (Nat.sub_le _ _)) ω] using hprev j hj
      · simpa [prefixVec_eq_partialSum X (show k ≤ k by rfl) ω] using hkge
  by_cases hω : ω ∈ firstHitEvent X t k
  · -- On the first-hit layer, both indicators are active and the payloads agree.
    have hset : (fun i : Fin k ↦ X i ω) ∈ firstHitPrefixSet k t := hmem.mpr hω
    simp [firstHitPrefixPayload, hset, hω, prefixVec_eq_partialSum X (show k ≤ k by rfl) ω]
  · -- Off the first-hit layer, both indicators vanish.
    have hset : (fun i : Fin k ↦ X i ω) ∉ firstHitPrefixSet k t := mt hmem.mp hω
    simp [firstHitPrefixPayload, hset, hω]

/-- Helper for Theorem 5.28: the concrete absolute first-hit payload factors through the first `k`
coordinates. -/
private lemma abs_first_hit_payload_comp (X : ℕ → Ω → ℝ) {k : ℕ} (_hk : 1 ≤ k) (t : ℝ) (ω : Ω) :
    absFirstHitPrefixPayload k t (fun i : Fin k ↦ X i ω) =
      Set.indicator (absFirstHitEvent X t k) (fun ω ↦ partialSum X k ω) ω := by
  -- Evaluate the tuple payload on the concrete prefix coordinates and rewrite the absolute prefix
  -- sums to the original partial sums.
  classical
  have hmem :
      (fun i : Fin k ↦ X i ω) ∈ absFirstHitPrefixSet k t ↔ ω ∈ absFirstHitEvent X t k := by
    constructor
    · intro hz
      refine ⟨?_, ?_⟩
      · intro j hj
        have hj' := Finset.mem_Icc.mp hj
        have hzj := Set.mem_iInter.1 (Set.mem_iInter.1 hz.1 j) hj
        simpa [prefixVec_eq_partialSum X (le_trans hj'.2 (Nat.sub_le _ _)) ω] using hzj
      · simpa [absFirstHitPrefixSet, prefixVec_eq_partialSum X (show k ≤ k by rfl) ω] using hz.2
    · intro hω
      rcases hω with ⟨hprev, hkge⟩
      refine ⟨?_, ?_⟩
      · refine Set.mem_iInter.2 fun j ↦ Set.mem_iInter.2 fun hj ↦ ?_
        have hj' := Finset.mem_Icc.mp hj
        simpa [prefixVec_eq_partialSum X (le_trans hj'.2 (Nat.sub_le _ _)) ω] using hprev j hj
      · simpa [prefixVec_eq_partialSum X (show k ≤ k by rfl) ω] using hkge
  by_cases hω : ω ∈ absFirstHitEvent X t k
  · -- On the absolute first-hit layer, both indicators are active and the payloads agree.
    have hset : (fun i : Fin k ↦ X i ω) ∈ absFirstHitPrefixSet k t := hmem.mpr hω
    simp [absFirstHitPrefixPayload, hset, hω, prefixVec_eq_partialSum X (show k ≤ k by rfl) ω]
  · -- Off the absolute first-hit layer, both indicators vanish.
    have hset : (fun i : Fin k ↦ X i ω) ∉ absFirstHitPrefixSet k t := mt hmem.mp hω
    simp [absFirstHitPrefixPayload, hset, hω]

/-- Helper for Theorem 5.28: the tuple-level future block sum. -/
private def futureVecSum (m : ℕ) (z : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, z i

-- Proof sketch: rewrite the future tuple as the `Ico k n` block and appeal to the tail-sum lemma.
/-- Helper for Theorem 5.28: summing the future `n - k` tuple coordinates gives the tail increment
`Sₙ - Sₖ`. -/
private lemma futureVecSum_eq_tail_increment (X : ℕ → Ω → ℝ) {k n : ℕ} (hk : k ≤ n) (ω : Ω) :
    futureVecSum (n - k) (fun i : Fin (n - k) ↦ X (k + i) ω) =
      partialSum X n ω - partialSum X k ω := by
  -- Reindex the future tuple sum as the `Ico k n` block appearing in `partialSum_sub_eq_sum_Ico`.
  rw [futureVecSum]
  calc
    ∑ i : Fin (n - k), X (k + i) ω
      = ∑ i ∈ Finset.range (n - k), X (k + i) ω := by
          simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ X (k + i) ω) (n - k))
    _ = ∑ i ∈ Finset.Ico k n, X i ω := by
          rw [Finset.sum_Ico_eq_sum_range]
    _ = partialSum X n ω - partialSum X k ω := by
          symm
          exact partialSum_sub_eq_sum_Ico X hk ω

/-- Helper for Theorem 5.28: summing the coordinates of a finite future block is measurable. -/
private lemma measurable_futureVecSum (m : ℕ) :
    Measurable (fun z : Fin m → ℝ ↦ futureVecSum m z) := by
  -- Unfold the finite sum and use measurability of each coordinate projection.
  unfold futureVecSum
  refine Finset.measurable_sum Finset.univ ?_
  intro i hi
  exact measurable_pi_apply i

/-- Helper for Theorem 5.28: the filtered past/future block independence can be reindexed to the
raw `Fin k` / `Fin (n - k)` tuple coordinates used by the first-hit payloads. -/
private lemma prefix_tuple_indep_future_tuple (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (n k : ℕ) (hk : k ≤ n) (hX_indep : iIndepFun (fun i : Fin n ↦ X i) P)
    (hX_memLp : ∀ i ∈ Finset.range n, MemLp (X i) 2 P)
    {φ : (Fin k → ℝ) → ℝ} {ψ : (Fin (n - k) → ℝ) → ℝ}
    (hφ : AEMeasurable φ (P.map (fun ω ↦ fun i : Fin k ↦ X i ω)))
    (hψ : AEMeasurable ψ (P.map (fun ω ↦ fun i : Fin (n - k) ↦ X (k + i) ω))) :
    IndepFun (fun ω ↦ φ (fun i : Fin k ↦ X i ω))
      (fun ω ↦ ψ (fun i : Fin (n - k) ↦ X (k + i) ω)) P := by
  let pastIdx : Finset (Fin n) := Finset.univ.filter (fun i : Fin n ↦ (i : ℕ) < k)
  let futureIdx : Finset (Fin n) := Finset.univ.filter (fun i : Fin n ↦ k ≤ (i : ℕ))
  let pastCoord : Ω → pastIdx → ℝ := fun ω i ↦ X i ω
  let futureCoord : Ω → futureIdx → ℝ := fun ω i ↦ X i ω
  let pastToPrefix : (pastIdx → ℝ) → (Fin k → ℝ) := fun z i ↦
    z ⟨⟨i, lt_of_lt_of_le i.2 hk⟩, by
      simp [pastIdx, i.2]⟩
  let futureToSuffix : (futureIdx → ℝ) → (Fin (n - k) → ℝ) := fun z i ↦
    z ⟨⟨k + i, by
      omega⟩, by
      simp [futureIdx]⟩
  have hPastCoord : AEMeasurable pastCoord P := by
    -- The filtered past tuple is a.e.-measurable coordinatewise.
    refine aemeasurable_pi_lambda _ fun i ↦ ?_
    exact (hX_memLp i (by simp)).aemeasurable
  have hFutureCoord : AEMeasurable futureCoord P := by
    -- The filtered future tuple is a.e.-measurable coordinatewise.
    refine aemeasurable_pi_lambda _ fun i ↦ ?_
    exact (hX_memLp i (by simp)).aemeasurable
  have hPastToPrefix : Measurable pastToPrefix := by
    -- Reindexing from the filtered past block to the raw `Fin k` tuple is coordinatewise
    -- evaluation at the matching past index.
    refine measurable_pi_lambda _ fun i ↦ ?_
    let idx : pastIdx := ⟨⟨i, lt_of_lt_of_le i.2 hk⟩, by
      simp [pastIdx, i.2]⟩
    simpa [pastToPrefix, idx] using
      (measurable_pi_apply idx : Measurable fun z : pastIdx → ℝ ↦ z idx)
  have hFutureToSuffix : Measurable futureToSuffix := by
    -- The same coordinatewise evaluation reindexes the filtered future block to `Fin (n - k)`.
    refine measurable_pi_lambda _ fun i ↦ ?_
    let idx : futureIdx := ⟨⟨k + i, by
      omega⟩, by
      simp [futureIdx]⟩
    simpa [futureToSuffix, idx] using
      (measurable_pi_apply idx : Measurable fun z : futureIdx → ℝ ↦ z idx)
  have hPrefixTuple : AEMeasurable (fun ω ↦ fun i : Fin k ↦ X i ω) P := by
    -- The raw prefix tuple is a.e.-measurable coordinatewise.
    refine aemeasurable_pi_lambda _ fun i ↦ ?_
    exact (hX_memLp i (Finset.mem_range.mpr (lt_of_lt_of_le i.2 hk))).aemeasurable
  have hFutureTuple : AEMeasurable (fun ω ↦ fun i : Fin (n - k) ↦ X (k + i) ω) P := by
    -- The raw future tuple is a.e.-measurable coordinatewise after shifting by `k`.
    refine aemeasurable_pi_lambda _ fun i ↦ ?_
    have hki : k + (i : ℕ) < n := by
      omega
    exact (hX_memLp (k + i) (Finset.mem_range.mpr hki)).aemeasurable
  have hFiltered :
      IndepFun pastCoord futureCoord P := by
    have hdisj : Disjoint pastIdx futureIdx := by
      -- The index split is by strict inequality versus the complementary weak inequality.
      refine Finset.disjoint_left.mpr ?_
      intro i hiPast hiFuture
      simp only [pastIdx, futureIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hiPast hiFuture
      exact hiPast.not_ge hiFuture
    -- Independence of the filtered past and future coordinate blocks comes directly from
    -- `iIndepFun.indepFun_finset₀`.
    have hbase := hX_indep.indepFun_finset₀ pastIdx futureIdx hdisj fun i ↦
      (hX_memLp i (by simp)).aemeasurable
    simpa [pastCoord, futureCoord] using hbase
  have hRawTuple :
      IndepFun (pastToPrefix ∘ pastCoord) (futureToSuffix ∘ futureCoord) P := by
    -- Compose the filtered tuple independence with the concrete reindexing maps.
    exact hFiltered.comp₀ hPastCoord hFutureCoord hPastToPrefix.aemeasurable
      hFutureToSuffix.aemeasurable
  have hRaw :
      IndepFun (fun ω ↦ fun i : Fin k ↦ X i ω)
        (fun ω ↦ fun i : Fin (n - k) ↦ X (k + i) ω) P := by
    -- The reindexed filtered tuples are definitionally the raw prefix and future tuples.
    simpa [Function.comp, pastToPrefix, futureToSuffix, pastCoord, futureCoord] using hRawTuple
  -- Apply the desired observables to the raw tuples.
  exact hRaw.comp₀ hPrefixTuple hFutureTuple hφ hψ

/-- Helper for Theorem 5.28: the one-sided first-hit payload is orthogonal to the terminal
future increment on each first-hit layer. -/
private lemma first_hit_cross_term_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (n : ℕ) (hX_indep : iIndepFun (fun i : Fin n ↦ X i) P)
    (hX_mean : ∀ i ∈ Finset.range n, P[X i] = 0)
    (hX_memLp : ∀ i ∈ Finset.range n, MemLp (X i) 2 P) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 n) (t c : ℝ) :
    P[fun ω ↦
      Set.indicator (firstHitEvent X t k) (fun ω ↦ partialSum X k ω + c) ω *
        (partialSum X n ω - partialSum X k ω)] = 0 := by
  let prefixTuple : Ω → Fin k → ℝ := fun ω i ↦ X i ω
  let futureTuple : Ω → Fin (n - k) → ℝ := fun ω i ↦ X (k + i) ω
  have hk_pos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk_le : k ≤ n := (Finset.mem_Icc.mp hk).2
  have hPrefixTuple : AEMeasurable prefixTuple P := by
    -- The concrete prefix tuple is a.e.-measurable coordinatewise.
    refine aemeasurable_pi_lambda _ fun i ↦ ?_
    exact (hX_memLp i (Finset.mem_range.mpr (lt_of_lt_of_le i.2 hk_le))).aemeasurable
  have hFutureTuple : AEMeasurable futureTuple P := by
    -- The concrete future tuple is a.e.-measurable coordinatewise after the shift by `k`.
    refine aemeasurable_pi_lambda _ fun i ↦ ?_
    have hki : k + (i : ℕ) < n := by
      omega
    exact (hX_memLp (k + i) (Finset.mem_range.mpr hki)).aemeasurable
  have hPayload :
      AEMeasurable (fun ω ↦ firstHitPrefixPayload k t c (prefixTuple ω)) P := by
    -- The first-hit payload is measurable on tuple space, hence a.e.-measurable after composing
    -- with the prefix tuple map.
    exact (measurable_firstHitPrefixPayload k t c).aemeasurable.comp_aemeasurable hPrefixTuple
  have hTail :
      AEMeasurable (fun ω ↦ futureVecSum (n - k) (futureTuple ω)) P := by
    -- The tail block sum is likewise measurable on tuple space and therefore a.e.-measurable.
    exact (measurable_futureVecSum (n - k)).aemeasurable.comp_aemeasurable hFutureTuple
  have hIndep :
      IndepFun (fun ω ↦ firstHitPrefixPayload k t c (prefixTuple ω))
        (fun ω ↦ futureVecSum (n - k) (futureTuple ω)) P := by
    -- The raw tuple independence bridge applies directly to the concrete first-hit payload and
    -- future block sum.
    exact prefix_tuple_indep_future_tuple P X n k hk_le hX_indep hX_memLp
      (measurable_firstHitPrefixPayload k t c).aemeasurable
      (measurable_futureVecSum (n - k)).aemeasurable
  have hTailZero : ∫ ω, futureVecSum (n - k) (futureTuple ω) ∂P = 0 := by
    have hnInt :
        Integrable (partialSum X n) P :=
      (partialSum_memLp_two P X (show n ≤ n by rfl) hX_memLp).integrable (by norm_num)
    have hkInt :
        Integrable (partialSum X k) P :=
      (partialSum_memLp_two P X hk_le hX_memLp).integrable (by norm_num)
    -- Rewrite the future block sum as the terminal increment and use that both partial sums are
    -- centered.
    calc
      ∫ ω, futureVecSum (n - k) (futureTuple ω) ∂P
        = ∫ ω, (partialSum X n ω - partialSum X k ω) ∂P := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall (fun ω ↦ futureVecSum_eq_tail_increment X hk_le ω)
      _ = (∫ ω, partialSum X n ω ∂P) - ∫ ω, partialSum X k ω ∂P := by
            rw [integral_sub hnInt hkInt]
      _ = 0 := by
            rw [partialSum_mean_zero P X (show n ≤ n by rfl) hX_mean hX_memLp,
              partialSum_mean_zero P X hk_le hX_mean hX_memLp]
            ring
  have hRewrite :
      (fun ω ↦ firstHitPrefixPayload k t c (prefixTuple ω) * futureVecSum (n - k) (futureTuple ω))
        =ᵐ[P]
      (fun ω ↦
        Set.indicator (firstHitEvent X t k) (fun ω ↦ partialSum X k ω + c) ω *
          (partialSum X n ω - partialSum X k ω)) := by
    -- The tuple payload and future sum rewrite pointwise to the textbook first-hit layer and tail
    -- increment.
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    simp [prefixTuple, futureTuple, first_hit_payload_comp X hk_pos t c ω,
      futureVecSum_eq_tail_increment X hk_le ω]
  -- Independence kills the mixed term because the tail increment still has mean zero.
  calc
    ∫ ω,
      Set.indicator (firstHitEvent X t k) (fun ω ↦ partialSum X k ω + c) ω *
        (partialSum X n ω - partialSum X k ω) ∂P
      = ∫ ω, firstHitPrefixPayload k t c (prefixTuple ω) * futureVecSum (n - k) (futureTuple ω) ∂P := by
          symm
          exact integral_congr_ae hRewrite
    _ =
        (∫ ω, firstHitPrefixPayload k t c (prefixTuple ω) ∂P) *
          ∫ ω, futureVecSum (n - k) (futureTuple ω) ∂P := by
            exact hIndep.integral_mul_eq_mul_integral hPayload.aestronglyMeasurable
              hTail.aestronglyMeasurable
    _ = 0 := by
          rw [hTailZero, mul_zero]

/-- Helper for Theorem 5.28: the absolute first-hit payload is orthogonal to the terminal future
increment on each absolute first-hit layer. -/
private lemma abs_first_hit_cross_term_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (n : ℕ) (hX_indep : iIndepFun (fun i : Fin n ↦ X i) P)
    (hX_mean : ∀ i ∈ Finset.range n, P[X i] = 0)
    (hX_memLp : ∀ i ∈ Finset.range n, MemLp (X i) 2 P) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 n) (t : ℝ) :
    P[fun ω ↦
      Set.indicator (absFirstHitEvent X t k) (fun ω ↦ partialSum X k ω) ω *
        (partialSum X n ω - partialSum X k ω)] = 0 := by
  let prefixTuple : Ω → Fin k → ℝ := fun ω i ↦ X i ω
  let futureTuple : Ω → Fin (n - k) → ℝ := fun ω i ↦ X (k + i) ω
  have hk_pos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk_le : k ≤ n := (Finset.mem_Icc.mp hk).2
  have hPrefixTuple : AEMeasurable prefixTuple P := by
    -- The concrete prefix tuple is a.e.-measurable coordinatewise.
    refine aemeasurable_pi_lambda _ fun i ↦ ?_
    exact (hX_memLp i (Finset.mem_range.mpr (lt_of_lt_of_le i.2 hk_le))).aemeasurable
  have hFutureTuple : AEMeasurable futureTuple P := by
    -- The concrete future tuple is a.e.-measurable coordinatewise after the shift by `k`.
    refine aemeasurable_pi_lambda _ fun i ↦ ?_
    have hki : k + (i : ℕ) < n := by
      omega
    exact (hX_memLp (k + i) (Finset.mem_range.mpr hki)).aemeasurable
  have hPayload :
      AEMeasurable (fun ω ↦ absFirstHitPrefixPayload k t (prefixTuple ω)) P := by
    -- The absolute first-hit payload is measurable on tuple space, hence a.e.-measurable after
    -- composing with the prefix tuple map.
    exact (measurable_absFirstHitPrefixPayload k t).aemeasurable.comp_aemeasurable hPrefixTuple
  have hTail :
      AEMeasurable (fun ω ↦ futureVecSum (n - k) (futureTuple ω)) P := by
    -- The tail block sum is measurable on tuple space and therefore a.e.-measurable.
    exact (measurable_futureVecSum (n - k)).aemeasurable.comp_aemeasurable hFutureTuple
  have hIndep :
      IndepFun (fun ω ↦ absFirstHitPrefixPayload k t (prefixTuple ω))
        (fun ω ↦ futureVecSum (n - k) (futureTuple ω)) P := by
    -- Reuse the same raw tuple independence bridge for the absolute first-hit payload.
    exact prefix_tuple_indep_future_tuple P X n k hk_le hX_indep hX_memLp
      (measurable_absFirstHitPrefixPayload k t).aemeasurable
      (measurable_futureVecSum (n - k)).aemeasurable
  have hTailZero : ∫ ω, futureVecSum (n - k) (futureTuple ω) ∂P = 0 := by
    have hnInt :
        Integrable (partialSum X n) P :=
      (partialSum_memLp_two P X (show n ≤ n by rfl) hX_memLp).integrable (by norm_num)
    have hkInt :
        Integrable (partialSum X k) P :=
      (partialSum_memLp_two P X hk_le hX_memLp).integrable (by norm_num)
    -- Rewrite the future block sum as the terminal increment and use that both partial sums are
    -- centered.
    calc
      ∫ ω, futureVecSum (n - k) (futureTuple ω) ∂P
        = ∫ ω, (partialSum X n ω - partialSum X k ω) ∂P := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall (fun ω ↦ futureVecSum_eq_tail_increment X hk_le ω)
      _ = (∫ ω, partialSum X n ω ∂P) - ∫ ω, partialSum X k ω ∂P := by
            rw [integral_sub hnInt hkInt]
      _ = 0 := by
            rw [partialSum_mean_zero P X (show n ≤ n by rfl) hX_mean hX_memLp,
              partialSum_mean_zero P X hk_le hX_mean hX_memLp]
            ring
  have hRewrite :
      (fun ω ↦ absFirstHitPrefixPayload k t (prefixTuple ω) * futureVecSum (n - k) (futureTuple ω))
        =ᵐ[P]
      (fun ω ↦
        Set.indicator (absFirstHitEvent X t k) (fun ω ↦ partialSum X k ω) ω *
          (partialSum X n ω - partialSum X k ω)) := by
    -- The tuple payload and future sum rewrite pointwise to the absolute first-hit layer and tail
    -- increment.
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    simp [prefixTuple, futureTuple, abs_first_hit_payload_comp X hk_pos t ω,
      futureVecSum_eq_tail_increment X hk_le ω]
  -- Independence kills the mixed term because the tail increment still has mean zero.
  calc
    ∫ ω,
      Set.indicator (absFirstHitEvent X t k) (fun ω ↦ partialSum X k ω) ω *
        (partialSum X n ω - partialSum X k ω) ∂P
      = ∫ ω, absFirstHitPrefixPayload k t (prefixTuple ω) * futureVecSum (n - k) (futureTuple ω) ∂P := by
          symm
          exact integral_congr_ae hRewrite
    _ =
        (∫ ω, absFirstHitPrefixPayload k t (prefixTuple ω) ∂P) *
          ∫ ω, futureVecSum (n - k) (futureTuple ω) ∂P := by
            exact hIndep.integral_mul_eq_mul_integral hPayload.aestronglyMeasurable
              hTail.aestronglyMeasurable
    _ = 0 := by
          rw [hTailZero, mul_zero]

/-- Helper for Theorem 5.28: the one-sided hit indicator is the sum of the disjoint one-sided
first-hit layer indicators. -/
private lemma first_hit_indicator_sum_eq_hit_indicator (X : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) :
    (fun ω ↦ Finset.sum (Finset.Icc 1 n)
      (fun k ↦ Set.indicator (firstHitEvent X t k) (fun _ ↦ (1 : ℝ)) ω)) =
      Set.indicator (oneSidedHitEvent X n t) (fun _ ↦ (1 : ℝ)) := by
  funext ω
  by_cases hω : ω ∈ oneSidedHitEvent X n t
  · rcases exists_firstHitEvent X n t ω hω with ⟨k, hk, hkω⟩
    -- On the hit event, exactly the first hitting layer contributes `1`.
    rw [Finset.sum_eq_single k]
    · simp [hω, hkω]
    · intro l hl hlk
      have hdisj := firstHitEvent_disjoint X hk hl hlk.symm t
      have hl_not : ω ∉ firstHitEvent X t l := by
        intro hlω
        exact (Set.disjoint_left.mp hdisj) hkω hlω
      simp [hl_not]
    · intro hk_not_mem
      exact False.elim (hk_not_mem hk)
  · have hnone : ∀ k ∈ Finset.Icc 1 n, ω ∉ firstHitEvent X t k := by
      intro k hk hkω
      exact hω ⟨k, hk, hkω.2⟩
    -- Off the hit event, all first-hit indicators vanish.
    have hsum :
        Finset.sum (Finset.Icc 1 n)
          (fun k ↦ Set.indicator (firstHitEvent X t k) (fun _ ↦ (1 : ℝ)) ω) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      simp [hnone k hk]
    rw [hsum]
    simp [hω]

/-- Helper for Theorem 5.28: the absolute hit indicator is the sum of the disjoint absolute
first-hit layer indicators. -/
private lemma abs_first_hit_indicator_sum_eq_hit_indicator (X : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) :
    (fun ω ↦ Finset.sum (Finset.Icc 1 n)
      (fun k ↦ Set.indicator (absFirstHitEvent X t k) (fun _ ↦ (1 : ℝ)) ω)) =
      Set.indicator (absHitEvent X n t) (fun _ ↦ (1 : ℝ)) := by
  funext ω
  by_cases hω : ω ∈ absHitEvent X n t
  · rcases exists_absFirstHitEvent X n t ω hω with ⟨k, hk, hkω⟩
    -- On the absolute hit event, exactly the first absolute hitting layer contributes `1`.
    rw [Finset.sum_eq_single k]
    · simp [hω, hkω]
    · intro l hl hlk
      have hdisj := absFirstHitEvent_disjoint X hk hl hlk.symm t
      have hl_not : ω ∉ absFirstHitEvent X t l := by
        intro hlω
        exact (Set.disjoint_left.mp hdisj) hkω hlω
      simp [hl_not]
    · intro hk_not_mem
      exact False.elim (hk_not_mem hk)
  · have hnone : ∀ k ∈ Finset.Icc 1 n, ω ∉ absFirstHitEvent X t k := by
      intro k hk hkω
      exact hω ⟨k, hk, hkω.2⟩
    -- Off the absolute hit event, all absolute first-hit indicators vanish.
    have hsum :
        Finset.sum (Finset.Icc 1 n)
          (fun k ↦ Set.indicator (absFirstHitEvent X t k) (fun _ ↦ (1 : ℝ)) ω) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      simp [hnone k hk]
    rw [hsum]
    simp [hω]

-- Proof sketch: decompose the event according to the first index `k` for which `partialSum X k`
-- exceeds `t`, use independence of the past and future increments, and optimize the resulting
-- bound with the choice `c = Var[partialSum X n; P] / t`.
/-- Theorem 5.28 (1): Kolmogorov's inequality (5.10). For independent centered square-integrable
real random variables, the probability that one of the partial sums `S₁, …, Sₙ` reaches the
level `t > 0` is bounded by `Var[Sₙ] / (t² + Var[Sₙ])`. This is the canonical `0`-based Lean
version for a sequence `X 0, X 1, …`; for the textbook sequence `X₁, X₂, …`, apply it to
`fun k ↦ X (k + 1)`. -/
theorem kolmogorov_inequality_partial_sums (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (n : ℕ) (hX_indep : iIndepFun (fun i : Fin n ↦ X i) P)
    (hX_mean : ∀ k ∈ Finset.range n, P[X k] = 0)
    (hX_memLp : ∀ k ∈ Finset.range n, MemLp (X k) 2 P) {t : ℝ} (ht : 0 < t) :
    P (oneSidedHitEvent X n t) ≤
      ENNReal.ofReal (Var[partialSum X n; P] / (t ^ 2 + Var[partialSum X n; P])) :=
  -- Route correction: the file now has the prefix `L²` control and the tail-block rewrite, so the
  -- remaining work is the stopped-square assembly itself: the raw tuple independence bridge, the
  -- mixed-term cancellation, and the exact first-hit indicator partition are now available above.
  -- TODO: integrate the textbook expansion of `(partialSum X n + c)^2` over the first-hit layers,
  -- drop the nonnegative tail-square term, rewrite the layer sum with
  -- `first_hit_indicator_sum_eq_hit_indicator`, and optimize with `c = Var[partialSum X n; P] / t`.
  sorry

-- Proof sketch: repeat the first-exit decomposition for the event that `|partialSum X k|` reaches
-- `t`, now with the stopped sets defined by the first index where the absolute value crosses the
-- threshold, and take `c = 0` in the same second-moment estimate.
/-- Theorem 5.28 (2): Kolmogorov's inequality (5.11). Under the same assumptions, the probability
that the absolute values of the partial sums `S₁, …, Sₙ` ever reach the level `t > 0` is bounded
by `Var[Sₙ] / t²`. This is the canonical `0`-based Lean version for a sequence `X 0, X 1, …`; for
the textbook sequence `X₁, X₂, …`, apply it to `fun k ↦ X (k + 1)`. -/
theorem kolmogorov_inequality_abs_partial_sums (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (n : ℕ) (hX_indep : iIndepFun (fun i : Fin n ↦ X i) P)
    (hX_mean : ∀ k ∈ Finset.range n, P[X k] = 0)
    (hX_memLp : ∀ k ∈ Finset.range n, MemLp (X k) 2 P) {t : ℝ} (ht : 0 < t) :
    P (absHitEvent X n t) ≤
      ENNReal.ofReal (Var[partialSum X n; P] / t ^ 2) :=
  -- Route correction: the absolute-value payload now also factors through the prefix tuple, so the
  -- remaining gap is the same stopped-square assembly as in the one-sided theorem.
  -- TODO: repeat the integrated first-hit expansion with the absolute payloads, use
  -- `abs_first_hit_cross_term_zero` and `abs_first_hit_indicator_sum_eq_hit_indicator`, and finish
  -- the `c = 0` case of the textbook second-moment argument.
  sorry
