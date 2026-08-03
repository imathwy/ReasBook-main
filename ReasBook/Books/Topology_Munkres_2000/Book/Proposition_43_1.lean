module

public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.UniformSpace.UniformEmbedding

public section

universe u

/- Proposition 43.1: A closed subset `A` of a complete metric space `X` is complete in the
restricted metric. -/
#check fun {X : Type u} [MetricSpace X] [CompleteSpace X] (A : Set X) (hA : IsClosed A) ↦
  hA.isComplete.completeSpace_coe

/- The proposition is the metric-space specialization of this canonical uniform-space instance. -/
#check IsClosed.completeSpace_coe
