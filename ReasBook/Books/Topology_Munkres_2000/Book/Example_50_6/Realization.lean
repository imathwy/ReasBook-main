module

public import Topology_Munkres_2000.Book.Example_50_6.LinearGraph
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Topology.Category.TopCat.Basic

@[expose] public section

universe u v

namespace SimpleGraph

/-- A topological linear-graph realization of a simple graph, with explicit vertex and
edge correspondences and the expected endpoint incidence relation. -/
structure LinearRealization {V : Type u} (G : SimpleGraph V) where
  Carrier : TopCat.{v}
  linearGraph : FiniteLinearGraph.{v, v} Carrier
  vertex : V → Carrier
  vertex_injective : Function.Injective vertex
  edgeEquiv : G.edgeSet ≃ linearGraph.Edge
  vertex_eq_endpoint_iff : ∀ (e : G.edgeSet) (x : V), x ∈ e.1 ↔
    vertex x = linearGraph.edge (edgeEquiv e) 0 ∨
      vertex x = linearGraph.edge (edgeEquiv e) 1

namespace LinearRealization

variable {V : Type u} {G : SimpleGraph V}

/-- The finite linear graph presentation stored by a simple graph realization. -/
def finiteLinearGraph (R : G.LinearRealization) : FiniteLinearGraph.{v, v} R.Carrier :=
  R.linearGraph

/-- A vertex is incident to an edge exactly when its realized point is an endpoint of
the corresponding realized arc. -/
theorem incident_iff_endpoint (R : G.LinearRealization) (e : G.edgeSet) (x : V) :
    x ∈ e.1 ↔ R.vertex x = R.finiteLinearGraph.edge (R.edgeEquiv e) 0 ∨
      R.vertex x = R.finiteLinearGraph.edge (R.edgeEquiv e) 1 := by
  -- Unfolding the accessor exposes the realization's stored incidence law.
  exact R.vertex_eq_endpoint_iff e x


end LinearRealization

end SimpleGraph
