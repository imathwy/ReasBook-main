module

public import Topology_Munkres_2000.Book.Exercise_16_5.ProductTopology
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

public section

open scoped Topology

/- Exercise 20.3 (1): The distance map of a metric space is continuous. -/
#check continuous_dist

/-- Helper for Exercise 20.3: continuity of the distance map implies continuity after fixing its
second argument. -/
private lemma continuous_dist_right_of_continuous_dist {X : Type u} [PseudoMetricSpace X]
    {t : TopologicalSpace X}
    (h : Continuous[TopologicalSpace.prod t t, inferInstance]
      (fun p : X × X ↦ dist p.1 p.2)) (x : X) :
    Continuous[t, inferInstance] (fun y : X ↦ dist y x) := by
  -- Insert the fixed point as the second coordinate and compose with the distance map.
  exact h.comp (continuous_id.prodMk continuous_const)

/-- Helper for Exercise 20.3: if the distance map is continuous for `t`, every pseudometric ball
is open for `t`. -/
private lemma isOpen_ball_of_continuous_dist {X : Type u} [PseudoMetricSpace X]
    {t : TopologicalSpace X}
    (h : Continuous[TopologicalSpace.prod t t, inferInstance]
      (fun p : X × X ↦ dist p.1 p.2)) (x : X) (ε : ℝ) :
    IsOpen[t] (Metric.ball x ε) := by
  -- A ball is the inverse image of an open lower ray under the fixed-coordinate distance map.
  exact (continuous_dist_right_of_continuous_dist h x).isOpen_preimage (Set.Iio ε) isOpen_Iio

/-- Exercise 20.3 (2), generalized to pseudometric spaces: if the distance map is continuous for
another topology on the same carrier, then that topology is finer than the pseudometric topology. -/
theorem topology_le_metricTopology_of_continuous_dist {X : Type u} [m : PseudoMetricSpace X]
    (t : TopologicalSpace X)
    (h : Continuous[TopologicalSpace.prod t t, inferInstance]
      (fun p : X × X ↦ dist p.1 p.2)) :
    t ≤ m.toUniformSpace.toTopologicalSpace := by
  -- Refine each point of a pseudometric-open set by a ball that is open for `t`.
  rw [TopologicalSpace.le_def]
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  rw [Metric.isOpen_iff] at hU
  obtain ⟨ε, hε, hball⟩ := hU x hx
  exact ⟨Metric.ball x ε, hball, isOpen_ball_of_continuous_dist h x ε,
    Metric.mem_ball_self hε⟩

/-- Exercise 20.3 (3), generalized to pseudometric spaces: the pseudometric topology is the coarsest
topology on `X` for which the distance map on `X × X` is continuous. -/
theorem continuous_dist_iff_topology_le_metricTopology {X : Type u} [m : PseudoMetricSpace X]
    (t : TopologicalSpace X) :
    Continuous[TopologicalSpace.prod t t, inferInstance]
        (fun p : X × X ↦ dist p.1 p.2) ↔
      t ≤ m.toUniformSpace.toTopologicalSpace := by
  constructor
  · -- Ball openness gives the forward topology comparison.
    exact topology_le_metricTopology_of_continuous_dist t
  · intro hle
    -- Continuity for the metric product topology persists after refining both domain factors.
    exact continuous_le_dom (TopologicalSpace.prod_mono hle hle) continuous_dist
