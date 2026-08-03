module

public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.MetricSpace.Defs

public section

open Set

universe u v

/-
Theorem 46.5. If `X` is compactly generated and `Y` is a metric space, then the
continuous functions from `X` to `Y` form a closed subset of the function space
with the topology of uniform convergence on compact subsets.
-/
#check fun {X : Type u} [TopologicalSpace X] [CompactlyCoherentSpace X]
    {Y : Type v} [MetricSpace Y] ↦
  UniformOnFun.isClosed_setOf_continuous CompactlyCoherentSpace.isCoherentWith
