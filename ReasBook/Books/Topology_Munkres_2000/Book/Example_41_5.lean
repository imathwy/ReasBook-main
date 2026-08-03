module

public import Topology_Munkres_2000.Book.Exercise_20_4.RealSequences
public import Topology_Munkres_2000.Book.Theorem_41_4.Paracompact
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.WithTopology

public section

namespace UniformRealSequence

/-- Example 41.5: Real sequence space with the uniform topology is metrizable. -/
instance metrizableSpace : TopologicalSpace.MetrizableSpace UniformRealSequence := by
  -- Equip the unwrapped sequence space with the metric defining the named uniform topology.
  letI : TopologicalSpace (ℕ → ℝ) := UniformMetric.topology ℕ
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  let unwrap : UniformRealSequence ≃ₜ (ℕ → ℝ) :=
    { WithTopology.equiv (ℕ → ℝ) (UniformMetric.topology ℕ) with
      continuous_toFun := WithTopology.continuous_ofTopology (UniformMetric.topology ℕ)
      continuous_invFun := WithTopology.continuous_toTopology (UniformMetric.topology ℕ) }
  -- Transfer the metric topology back along the canonical unwrapping homeomorphism.
  exact unwrap.isEmbedding.metrizableSpace

end UniformRealSequence

/- Example 41.5 (1): The space `ℕ → ℝ` is paracompact in the product topology. -/
#check (inferInstance : ParacompactSpace (ℕ → ℝ))

/- Example 41.5 (2): The space `ℕ → ℝ` is paracompact in the uniform topology. -/
#check (inferInstance : ParacompactSpace UniformRealSequence)

/- Example 41.5 (3): The source reports that paracompactness of `ℕ → ℝ` in the box
topology is unknown, so this displays only the proposition and asserts neither polarity. -/
#check ParacompactSpace BoxRealSequence
