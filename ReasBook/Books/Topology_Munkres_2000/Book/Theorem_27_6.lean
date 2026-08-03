module

public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

public section

/-- Theorem 27.6 (Uniform continuity theorem). A continuous map from a compact metric
space to a metric space is uniformly continuous. -/
theorem uniformContinuous_of_continuous_compact {X : Type u} {Y : Type v}
    [MetricSpace X] [CompactSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    UniformContinuous f := CompactSpace.uniformContinuous_of_continuous hf
