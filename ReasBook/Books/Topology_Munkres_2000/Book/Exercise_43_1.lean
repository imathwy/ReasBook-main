module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.UniformSpace.CompleteSeparated
public import Mathlib.Topology.UniformSpace.UniformEmbedding

public section

universe u

/-- The first assertion of Exercise 43.1: if one fixed positive-radius open ball around every point
has compact closure, then the metric space is complete. -/
theorem completeSpace_of_compactBallClosures
    {X : Type u} [MetricSpace X] (ε : ℝ) (hε : 0 < ε)
    (hcompact : ∀ x : X, IsCompact (closure (Metric.ball x ε))) :
    CompleteSpace X := by
  -- Trap a shifted tail of an arbitrary Cauchy sequence in one compact closure.
  apply Metric.complete_of_cauchySeq_tendsto
  intro v hv
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff'.mp hv) ε hε
  have htail_mem : ∀ n, v (n + N) ∈ closure (Metric.ball (v N) ε) := by
    intro n
    apply subset_closure
    rw [Metric.mem_ball]
    exact hN (n + N) (Nat.le_add_left N n)
  have htail_cauchy : CauchySeq (fun n ↦ v (n + N)) :=
    (cauchySeq_shift N).mpr hv
  obtain ⟨a, -, ha⟩ :=
    cauchySeq_tendsto_of_isComplete (hcompact (v N)).isComplete htail_mem htail_cauchy
  -- The shift is cofinal, so the original Cauchy sequence has the same limit.
  refine ⟨a, tendsto_nhds_of_cauchySeq_of_subseq hv ?_ ha⟩
  exact Filter.tendsto_add_atTop_nat N

/-- Every point of the open unit interval has a positive-radius open ball with
compact closure. -/
theorem openUnitInterval_exists_compactBallClosure
    (x : Set.Ioo (-1 : ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ IsCompact (closure (Metric.ball x ε)) := by
  -- Local compactness of the open subtype supplies a compact closed ball.
  letI : LocallyCompactSpace (Set.Ioo (-1 : ℝ) 1) := isOpen_Ioo.locallyCompactSpace
  obtain ⟨ε, hε, hclosedBall⟩ := Metric.exists_isCompact_closedBall x
  refine ⟨ε, hε, ?_⟩
  -- The closure of the open ball is a closed subset of that compact ball.
  exact hclosedBall.of_isClosed_subset isClosed_closure Metric.closure_ball_subset_closedBall

/-- Exercise 43.1 (2): The open unit interval has a compact-closure ball around
each point, but it is not complete. -/
theorem openUnitInterval_compactBallClosures_not_complete :
    (∀ x : Set.Ioo (-1 : ℝ) 1,
      ∃ ε : ℝ, 0 < ε ∧ IsCompact (closure (Metric.ball x ε))) ∧
      ¬ CompleteSpace (Set.Ioo (-1 : ℝ) 1) := by
  constructor
  · exact openUnitInterval_exists_compactBallClosure
  · intro hcomplete
    -- A complete subtype of a metric space is closed in the ambient space.
    have hinterval_complete : IsComplete (Set.Ioo (-1 : ℝ) 1) :=
      completeSpace_coe_iff_isComplete.mp hcomplete
    have hinterval_closed : IsClosed (Set.Ioo (-1 : ℝ) 1) :=
      hinterval_complete.isClosed
    -- The nonempty open interval cannot be closed.
    have hminusOne_lt_one : (-1 : ℝ) < 1 := by
      norm_num
    exact (not_le_of_gt hminusOne_lt_one) (isClosed_Ioo_iff.mp hinterval_closed)

end
