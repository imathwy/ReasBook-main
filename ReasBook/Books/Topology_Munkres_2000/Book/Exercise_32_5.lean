module

public import Topology_Munkres_2000.Book.Exercise_20_4.RealSequences
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.WithTopology

public section

/- Exercise 32.5 (1): The real sequence space `ℕ → ℝ` is normal in the product
topology. -/
#check (inferInstance : T4Space (ℕ → ℝ))

namespace UniformRealSequence

/-- Helper for Exercise 32.5: the uniform metric topology on real sequences is a `T4Space`. -/
theorem uniformMetricT4Space : @T4Space (ℕ → ℝ) (UniformMetric.topology ℕ) := by
  -- Install the metric whose induced topology is definitionally the named uniform topology.
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  -- Every metric space is normal and `T1`.
  exact Metric.t4Space

/-- Helper for Exercise 32.5: wrapping a raw sequence with the uniform topology is continuous. -/
theorem continuousUniformTopologyWrapper :
    @Continuous (ℕ → ℝ) UniformRealSequence (UniformMetric.topology ℕ) inferInstance
      (WithTopology.toTopology (UniformMetric.topology ℕ)) := by
  -- Apply the canonical continuity theorem with the raw topology fixed explicitly.
  exact WithTopology.continuous_toTopology _

/-- Helper for Exercise 32.5: unwrapping a uniformly topologized sequence is continuous. -/
theorem continuousUniformTopologyUnwrapper :
    @Continuous UniformRealSequence (ℕ → ℝ) inferInstance (UniformMetric.topology ℕ)
      WithTopology.ofTopology := by
  -- Apply the inverse canonical continuity theorem with the raw topology fixed explicitly.
  exact WithTopology.continuous_ofTopology _

/-- Helper for Exercise 32.5: the raw uniform metric space is homeomorphic to its
`UniformRealSequence` wrapper. -/
noncomputable def uniformTopologyHomeomorph :
    @Homeomorph (ℕ → ℝ) UniformRealSequence (UniformMetric.topology ℕ) inferInstance :=
  @Homeomorph.mk (ℕ → ℝ) UniformRealSequence (UniformMetric.topology ℕ) inferInstance
    ((WithTopology.equiv (ℕ → ℝ) (UniformMetric.topology ℕ)).symm :
      (ℕ → ℝ) ≃ UniformRealSequence)
    continuousUniformTopologyWrapper continuousUniformTopologyUnwrapper

/-- Exercise 32.5 (2): The real sequence space `ℕ → ℝ` is normal in the uniform
topology. -/
instance instT4Space : T4Space UniformRealSequence := by
  -- Transfer the separation property across the canonical homeomorphism.
  exact @Homeomorph.t4Space (ℕ → ℝ) UniformRealSequence
    (UniformMetric.topology ℕ) inferInstance uniformMetricT4Space uniformTopologyHomeomorph

end UniformRealSequence
