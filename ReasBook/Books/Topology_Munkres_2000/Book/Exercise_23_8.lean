module

public import Topology_Munkres_2000.Book.Exercise_20_4.RealSequences
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.WithTopology

public section

open scoped Topology

namespace UniformRealSequence

/-- Helper for Exercise 23.8: the uniformly topologized sequences with bounded range. -/
def boundedSequences : Set UniformRealSequence :=
  {x | Bornology.IsBounded (Set.range x.ofTopology)}

/-- Helper for Exercise 23.8: balls for the explicit uniform metric are open in the
uniform topology. -/
lemma uniformBall_isOpen (x : ℕ → ℝ) (ε : ℝ) :
    IsOpen[UniformMetric.topology ℕ] {y | (UniformMetric.metricSpace ℕ).dist y x < ε} := by
  -- Install the named uniform metric only while invoking the metric-ball API.
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  exact Metric.isOpen_ball

/-- Helper for Exercise 23.8: uniform distance below `1` bounds every ordinary
coordinate distance by the uniform distance. -/
lemma coordinateDistance_le_uniformDistance {x y : ℕ → ℝ}
    (hxy : (UniformMetric.metricSpace ℕ).dist x y < 1) (n : ℕ) :
    dist (x n) (y n) ≤ (UniformMetric.metricSpace ℕ).dist x y := by
  -- First compare the truncated coordinate distance with the defining supremum.
  have hbounded : BddAbove (Set.range fun k : ℕ ↦ min (dist (x k) (y k)) 1) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact min_le_right _ _
  have hmin : min (dist (x n) (y n)) 1 ≤ (UniformMetric.metricSpace ℕ).dist x y := by
    rw [UniformMetric.dist_eq]
    exact le_ciSup hbounded n
  -- Since the supremum is below `1`, truncation is inactive at this coordinate.
  have hcoord : dist (x n) (y n) < 1 := by
    by_contra hnot
    have hone : 1 ≤ dist (x n) (y n) := le_of_not_gt hnot
    rw [min_eq_right hone] at hmin
    exact (not_lt_of_ge hmin) hxy
  rwa [min_eq_left hcoord.le] at hmin

/-- Helper for Exercise 23.8: moving a uniformly bounded distance preserves boundedness
of the range. -/
lemma isBounded_range_of_uniformDistance_lt_one {x y : ℕ → ℝ}
    (hxy : (UniformMetric.metricSpace ℕ).dist x y < 1)
    (hx : Bornology.IsBounded (Set.range x)) :
    Bornology.IsBounded (Set.range y) := by
  -- Use the pairwise-distance characterization of bounded ranges.
  rw [Metric.isBounded_range_iff] at hx ⊢
  obtain ⟨C, hC⟩ := hx
  refine ⟨C + 2, fun n m ↦ ?_⟩
  have hyn : dist (y n) (x n) ≤ 1 := by
    rw [dist_comm]
    exact (coordinateDistance_le_uniformDistance hxy n).trans (UniformMetric.dist_le_one x y)
  have hym : dist (x m) (y m) ≤ 1 :=
    (coordinateDistance_le_uniformDistance hxy m).trans (UniformMetric.dist_le_one x y)
  calc
    dist (y n) (y m) ≤ dist (y n) (x n) + dist (x n) (y m) := dist_triangle _ _ _
    _ ≤ dist (y n) (x n) + (dist (x n) (x m) + dist (x m) (y m)) := by
      exact add_le_add_right (dist_triangle (x n) (x m) (y m)) (dist (y n) (x n))
    _ ≤ C + 2 := by
      linarith [hC n m]

/-- Helper for Exercise 23.8: uniform distance below `1` preserves boundedness of
the range in both directions. -/
lemma isBounded_range_iff_of_uniformDistance_lt_one {x y : ℕ → ℝ}
    (hxy : (UniformMetric.metricSpace ℕ).dist x y < 1) :
    Bornology.IsBounded (Set.range x) ↔ Bornology.IsBounded (Set.range y) := by
  -- Apply the one-way estimate twice, using symmetry of the uniform metric.
  constructor
  · exact isBounded_range_of_uniformDistance_lt_one hxy
  · intro hy
    apply isBounded_range_of_uniformDistance_lt_one
    · rwa [(UniformMetric.metricSpace ℕ).dist_comm]
    · exact hy

/-- Helper for Exercise 23.8: bounded sequences form a clopen subset of the uniform
sequence space. -/
lemma boundedSequences_isClopen : IsClopen boundedSequences := by
  -- A radius-one uniform ball cannot change boundedness of the underlying range.
  have hopen : IsOpen boundedSequences := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    refine ⟨{y | (UniformMetric.metricSpace ℕ).dist y.ofTopology x.ofTopology < 1}, ?_, ?_, ?_⟩
    · intro y hy
      rw [boundedSequences, Set.mem_setOf_eq] at hx ⊢
      exact (isBounded_range_iff_of_uniformDistance_lt_one hy).mpr hx
    · rw [WithTopology.isOpen_iff]
      simpa only [Set.preimage_setOf_eq, WithTopology.ofTopology_toTopology] using
        uniformBall_isOpen x.ofTopology 1
    · simp
  have hopen_compl : IsOpen boundedSequencesᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    refine ⟨{y | (UniformMetric.metricSpace ℕ).dist y.ofTopology x.ofTopology < 1}, ?_, ?_, ?_⟩
    · intro y hy hybounded
      apply hx
      rw [Set.mem_compl_iff, boundedSequences, Set.mem_setOf_eq] at hx
      rw [boundedSequences, Set.mem_setOf_eq] at hybounded ⊢
      exact (isBounded_range_iff_of_uniformDistance_lt_one hy).mp hybounded
    · rw [WithTopology.isOpen_iff]
      simpa only [Set.preimage_setOf_eq, WithTopology.ofTopology_toTopology] using
        uniformBall_isOpen x.ofTopology 1
    · simp
  -- Openness of the complement supplies closedness of the bounded-sequence set.
  exact ⟨isOpen_compl_iff.mp hopen_compl, hopen⟩

/-- Helper for Exercise 23.8: the natural-number sequence has unbounded range. -/
lemma natCastSequence_not_mem_boundedSequences :
    ofSequence (fun n : ℕ ↦ (n : ℝ)) ∉ boundedSequences := by
  -- A pairwise bound would be violated by a sufficiently large natural number.
  intro hbounded
  rw [boundedSequences, Set.mem_setOf_eq, Metric.isBounded_range_iff] at hbounded
  obtain ⟨C, hC⟩ := hbounded
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hdist := hC n 0
  rw [ofSequence_eq_toTopology, WithTopology.ofTopology_toTopology] at hdist
  norm_num [Real.dist_eq] at hdist
  linarith

/-- Exercise 23.8: The space of real sequences with the uniform topology is not connected. -/
theorem notConnected : ¬ ConnectedSpace UniformRealSequence := by
  -- Connectedness would force the clopen bounded-sequence set to be trivial.
  intro hconnected
  have htrivial := (connectedSpace_iff_clopen.mp hconnected).2 boundedSequences
    boundedSequences_isClopen
  have hzero : ofSequence (fun _ : ℕ ↦ 0) ∈ boundedSequences := by
    rw [boundedSequences, Set.mem_setOf_eq, Metric.isBounded_range_iff]
    refine ⟨0, ?_⟩
    intro n m
    rw [ofSequence_eq_toTopology, WithTopology.ofTopology_toTopology]
    simp
  -- The zero sequence rules out emptiness, while the natural-cast sequence rules out universality.
  rcases htrivial with hempty | huniv
  · rw [hempty] at hzero
    exact hzero
  · apply natCastSequence_not_mem_boundedSequences
    rw [huniv]
    exact Set.mem_univ _

end UniformRealSequence
