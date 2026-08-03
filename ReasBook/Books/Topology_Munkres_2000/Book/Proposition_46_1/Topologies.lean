module

public import Mathlib.Topology.UniformSpace.CompactConvergence

public section

open Set

universe u v

namespace FunctionTopology

/-- The topology of uniform convergence, transported to the common carrier `X → Y`. -/
@[expose, reducible]
def uniform (X : Type u) (Y : Type v) [UniformSpace Y] : TopologicalSpace (X → Y) :=
  TopologicalSpace.induced UniformFun.ofFun (UniformFun.topologicalSpace X Y)

/-- The topology of compact convergence, transported to the common carrier `X → Y`. -/
@[expose, reducible]
def compact (X : Type u) (Y : Type v) [TopologicalSpace X] [UniformSpace Y] :
    TopologicalSpace (X → Y) :=
  TopologicalSpace.induced (UniformOnFun.ofFun {K : Set X | IsCompact K})
    (UniformOnFun.topologicalSpace X Y {K : Set X | IsCompact K})

/-- The topology of compact convergence for an explicitly chosen uniformity on the codomain. -/
abbrev compactWith (X : Type u) (Y : Type v) [TopologicalSpace X]
    (uniformity : UniformSpace Y) : TopologicalSpace (X → Y) :=
  @compact X Y _ uniformity

end FunctionTopology
