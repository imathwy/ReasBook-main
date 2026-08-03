module

public import Topology_Munkres_2000.Book.Definition_53_1
public import Mathlib.Topology.Covering.Basic

public section

universe u v

/-- Remark 53.2: Every fiber of a covering map has the discrete topology induced
from the total space. -/
theorem IsCoveringMap.discreteTopology_fiber {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
    (hp : IsCoveringMap p) (b : B) : DiscreteTopology (p ⁻¹' {b}) :=
  (hp b).discreteTopology_fiber
