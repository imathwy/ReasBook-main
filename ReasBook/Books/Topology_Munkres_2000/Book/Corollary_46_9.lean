module

public import Topology_Munkres_2000.Book.Theorem_46_8.Comparison
public import Mathlib.Topology.MetricSpace.Defs

public section

universe u v

namespace ContinuousMap

/-- Corollary 46.9. Two metrics on `Y` inducing the same topology determine the same
compact-convergence topology on `C(X, Y)`. -/
theorem compactConvergence_eq_of_inducedTopology_eq {X : Type u} {Y : Type v}
    [TopologicalSpace X] [topologyY : TopologicalSpace Y] (m m' : MetricSpace Y)
    (hm : m.toUniformSpace.toTopologicalSpace = topologyY)
    (hm' : m'.toUniformSpace.toTopologicalSpace = topologyY) :
    TopologicalSpace.induced (fun f : C(X, Y) ↦ f.toFun)
        (FunctionTopology.compactWith X Y m.toUniformSpace) =
      TopologicalSpace.induced (fun f : C(X, Y) ↦ f.toFun)
        (FunctionTopology.compactWith X Y m'.toUniformSpace) := by
  rw [← compactOpen_eq_induced_compactWith m.toUniformSpace hm,
    ← compactOpen_eq_induced_compactWith m'.toUniformSpace hm']

end ContinuousMap
