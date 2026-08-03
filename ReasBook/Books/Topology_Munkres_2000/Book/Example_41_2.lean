module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Order.DenselyOrdered

public section

/-- Example 41.2: The open unit interval is a paracompact subspace of the Hausdorff
space `ℝ`, but it is not closed in `ℝ`. -/
theorem openUnitInterval_paracompact_not_isClosed :
    T2Space ℝ ∧ ParacompactSpace (Set.Ioo (0 : ℝ) 1) ∧
      ¬ IsClosed (Set.Ioo (0 : ℝ) 1) :=
  ⟨inferInstance, inferInstance, by simp⟩
