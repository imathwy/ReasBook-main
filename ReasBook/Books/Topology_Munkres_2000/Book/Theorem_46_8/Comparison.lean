module

public import Topology_Munkres_2000.Book.Proposition_46_1.Topologies

public section

universe u v

namespace ContinuousMap

/-- The compact-open topology on continuous maps is induced by the topology of compact
convergence on the ambient function space. -/
theorem compactOpen_eq_induced_compact {X : Type u} {Y : Type v} [TopologicalSpace X]
    [UniformSpace Y] :
    (compactOpen : TopologicalSpace C(X, Y)) =
      TopologicalSpace.induced (fun f : C(X, Y) ↦ f.toFun) (FunctionTopology.compact X Y) := by
  rw [FunctionTopology.compact, induced_compose]
  exact isUniformEmbedding_toUniformOnFunIsCompact.isInducing.eq_induced

/-- The compact-open topology agrees with compact convergence for any explicitly chosen
uniformity inducing the given topology on the codomain. -/
theorem compactOpen_eq_induced_compactWith {X : Type u} {Y : Type v} [TopologicalSpace X]
    [topologyY : TopologicalSpace Y] (uniformity : UniformSpace Y)
    (h : uniformity.toTopologicalSpace = topologyY) :
    (compactOpen : TopologicalSpace C(X, Y)) =
      TopologicalSpace.induced (fun f : C(X, Y) ↦ f.toFun)
        (FunctionTopology.compactWith X Y uniformity) := by
  subst topologyY
  exact @compactOpen_eq_induced_compact X Y _ uniformity

end ContinuousMap
