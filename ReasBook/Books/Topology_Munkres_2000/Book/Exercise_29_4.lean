module

public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.UnitInterval

public section

open Set
open scoped UniformConvergence

/-- Helper for Exercise 29.4: the constant-zero element of the uniform function space. -/
private def zeroSequence : ℕ →ᵤ Icc (0 : ℝ) 1 :=
  -- View the ordinary constant function as a uniformly topologized function.
  UniformFun.ofFun (fun _ ↦ 0)

/-- Helper for Exercise 29.4: the sequence supported at one coordinate with value `a`. -/
private def coordinateSpike (a : Icc (0 : ℝ) 1) (n : ℕ) : ℕ →ᵤ Icc (0 : ℝ) 1 :=
  -- Updating the zero function isolates the distinguished coordinate.
  UniformFun.ofFun (Function.update (fun _ ↦ 0) n a)

/-- Helper for Exercise 29.4: every positive real bounds a positive point of `Icc 0 1`. -/
private lemma exists_unitInterval_pos_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ a : Icc (0 : ℝ) 1, 0 < (a : ℝ) ∧ (a : ℝ) < ε := by
  -- Choose a real strictly between zero and both upper bounds.
  have hmin : 0 < min ε 1 := lt_min hε zero_lt_one
  obtain ⟨x, hx0, hxmin⟩ := exists_between hmin
  have hxε : x < ε := hxmin.trans_le (min_le_left ε 1)
  have hx1 : x ≤ 1 := (hxmin.trans_le (min_le_right ε 1)).le
  have hxmem : x ∈ Icc (0 : ℝ) 1 := ⟨hx0.le, hx1⟩
  -- Projecting to the interval avoids exposing the subtype constructor in the witness.
  refine ⟨Set.projIcc 0 1 zero_le_one x, ?_, ?_⟩
  · rw [Set.projIcc_of_mem zero_le_one hxmem]
    exact hx0
  · rw [Set.projIcc_of_mem zero_le_one hxmem]
    exact hxε

/-- Helper for Exercise 29.4: a coordinate spike is exactly its height from zero. -/
private lemma coordinateSpike_dist_zeroSequence (a : Icc (0 : ℝ) 1) (n : ℕ) :
    dist (coordinateSpike a n) zeroSequence = (a : ℝ) := by
  -- Bound the uniform distance above by checking every coordinate separately.
  have hupper : dist (coordinateSpike a n) zeroSequence ≤ (a : ℝ) := by
    refine (UniformFun.dist_le a.2.1).2 ?_
    intro i
    by_cases hi : i = n
    · subst i
      simp only [coordinateSpike, zeroSequence, UniformFun.toFun_ofFun,
        Function.update_apply, if_pos, Subtype.dist_eq, Set.Icc.coe_zero, Real.dist_eq,
        sub_zero, abs_of_nonneg a.2.1, le_refl]
    · simp only [coordinateSpike, zeroSequence, UniformFun.toFun_ofFun,
        Function.update_apply, if_neg hi, dist_self, a.2.1]
  -- Evaluation at the spike coordinate supplies the matching lower bound.
  have hlower : (a : ℝ) ≤ dist (coordinateSpike a n) zeroSequence := by
    calc
      (a : ℝ) = dist a (0 : Icc (0 : ℝ) 1) := by
        simp only [Subtype.dist_eq, Set.Icc.coe_zero, Real.dist_eq, sub_zero,
          abs_of_nonneg a.2.1]
      _ = dist (UniformFun.toFun (coordinateSpike a n) n)
          (UniformFun.toFun zeroSequence n) := by
        simp only [coordinateSpike, zeroSequence, UniformFun.toFun_ofFun,
          Function.update_apply, if_pos]
      _ ≤ dist (coordinateSpike a n) zeroSequence :=
        (UniformFun.dist_le dist_nonneg).mp le_rfl n
  exact le_antisymm hupper hlower

/-- Helper for Exercise 29.4: distinct coordinate spikes are separated by their height. -/
private lemma coordinateSpike_pairwise_le_dist (a : Icc (0 : ℝ) 1) :
    Pairwise (fun m n : ℕ ↦ (a : ℝ) ≤ dist (coordinateSpike a m) (coordinateSpike a n)) := by
  -- Evaluate two distinct spikes at the support of the first one.
  intro m n hmn
  calc
    (a : ℝ) = dist (UniformFun.toFun (coordinateSpike a m) m)
        (UniformFun.toFun (coordinateSpike a n) m) := by
      simp only [coordinateSpike, UniformFun.toFun_ofFun, Function.update_apply,
        if_pos, if_neg hmn, Subtype.dist_eq, Set.Icc.coe_zero, Real.dist_eq, sub_zero,
        abs_of_nonneg a.2.1]
    _ ≤ dist (coordinateSpike a m) (coordinateSpike a n) :=
      (UniformFun.dist_le dist_nonneg).mp le_rfl m

/-- Exercise 29.4: The countable power `[0, 1] ^ ℕ` with the uniform topology is not
locally compact. -/
theorem closedUnitIntervalSequencesNotLocallyCompact :
    ¬ LocallyCompactSpace (ℕ →ᵤ Icc (0 : ℝ) 1) := by
  -- A compact neighborhood of zero would contain a small uniform ball.
  intro hlocal
  letI : LocallyCompactSpace (ℕ →ᵤ Icc (0 : ℝ) 1) := hlocal
  obtain ⟨K, hK_nhds, _, hK_compact⟩ :=
    local_compact_nhds (x := zeroSequence) Filter.univ_mem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hK_nhds
  obtain ⟨a, ha_pos, ha_lt⟩ := exists_unitInterval_pos_lt ε hε
  -- Every spike of height `a` lies in that compact neighborhood.
  have hspikes : ∀ n, coordinateSpike a n ∈ K := by
    intro n
    apply hball
    rw [Metric.mem_ball, coordinateSpike_dist_zeroSequence]
    exact ha_lt
  -- Their uniform separation makes the spike family a closed copy of the discrete naturals.
  have hclosed : Topology.IsClosedEmbedding (coordinateSpike a) :=
    Metric.isClosedEmbedding_of_pairwise_le_dist ha_pos
      (coordinateSpike_pairwise_le_dist a)
  have hpreimage_compact : IsCompact (coordinateSpike a ⁻¹' K) :=
    hclosed.isCompact_preimage hK_compact
  have hpreimage_eq : coordinateSpike a ⁻¹' K = (univ : Set ℕ) :=
    eq_univ_of_forall hspikes
  -- The compact preimage would make the infinite set of naturals finite.
  have hfinite : (univ : Set ℕ).Finite := by
    rw [← hpreimage_eq]
    exact hpreimage_compact.finite_of_discrete
  exact Set.infinite_univ hfinite
