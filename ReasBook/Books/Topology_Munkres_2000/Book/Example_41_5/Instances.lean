module

public import Topology_Munkres_2000.Book.Exercise_20_4.RealSequences
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.WithTopology

public section

namespace UniformRealSequence

/-- Real sequence space with the uniform topology is metrizable. -/
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

end
