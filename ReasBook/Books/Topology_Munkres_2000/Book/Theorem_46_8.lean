module

public import Topology_Munkres_2000.Book.Theorem_46_8.Comparison
public import Mathlib.Topology.MetricSpace.Defs

public section

universe u v

namespace ContinuousMap

/-- Theorem 46.8. On `C(X, Y)`, the compact-open topology coincides with the topology
induced by compact convergence on `X → Y`. -/
theorem compactOpen_eq_compactConvergence {X : Type u} {Y : Type v} [TopologicalSpace X]
    [MetricSpace Y] :
    (compactOpen : TopologicalSpace C(X, Y)) =
      TopologicalSpace.induced (fun f : C(X, Y) ↦ f.toFun) (FunctionTopology.compact X Y) :=
  compactOpen_eq_induced_compact

end ContinuousMap
