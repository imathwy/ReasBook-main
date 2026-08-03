module

public import Mathlib.Topology.UnitInterval

@[expose] public section

universe u v

/-- A finite linear graph presentation on a topological space, including its Hausdorff
property, given by finitely many
embedded copies of the closed unit interval that cover the space and whose distinct
images meet in at most one point, necessarily an endpoint of both. -/
structure FiniteLinearGraph (X : Type u) [TopologicalSpace X] where
  t2Space : T2Space X
  Edge : Type v
  edgeFinite : Finite Edge
  edge : Edge → unitInterval → X
  edgeEmbedding : ∀ i, Topology.IsEmbedding (edge i)
  iUnion_range : ⋃ i, Set.range (edge i) = Set.univ
  interSubsetEndpoints : ∀ {i j}, i ≠ j →
    Set.range (edge i) ∩ Set.range (edge j) ⊆
      ({edge i 0, edge i 1} ∩ {edge j 0, edge j 1} : Set X)
  interSubsingleton : ∀ {i j}, i ≠ j →
    (Set.range (edge i) ∩ Set.range (edge j)).Subsingleton

namespace FiniteLinearGraph

variable {X : Type u} [TopologicalSpace X]

/-- The image of one parameterized edge of a finite linear graph. -/
def edgeSet (G : FiniteLinearGraph.{u, v} X) (i : G.Edge) : Set X :=
  Set.range (G.edge i)

/-- The edge set is the range of its stored unit-interval parameterization. -/
theorem edgeSet_def (G : FiniteLinearGraph.{u, v} X) (i : G.Edge) :
    G.edgeSet i = Set.range (G.edge i) := by
  -- The public edge-set accessor has this range as its defining value.
  rfl

/-- The vertices of a finite linear graph are all endpoint images of its edges. -/
def vertexSet (G : FiniteLinearGraph.{u, v} X) : Set X :=
  ⋃ i, {G.edge i 0, G.edge i 1}

/-- The vertex set is the union of the endpoint pairs of all edges. -/
theorem vertexSet_def (G : FiniteLinearGraph.{u, v} X) :
    G.vertexSet = ⋃ i, {G.edge i 0, G.edge i 1} := by
  -- The public vertex-set accessor is definitionally the endpoint union.
  rfl

/-- The edge sets of a finite linear graph cover its carrier. -/
theorem iUnion_edgeSet (G : FiniteLinearGraph.{u, v} X) :
    ⋃ i, G.edgeSet i = Set.univ := by
  -- After unfolding `edgeSet`, this is the covering field of the presentation.
  exact G.iUnion_range

/-- Each endpoint image of an edge is a vertex of the finite linear graph. -/
theorem endpoint_mem_vertexSet (G : FiniteLinearGraph.{u, v} X) (i : G.Edge)
    (x : unitInterval) (hx : x = 0 ∨ x = 1) :
    G.edge i x ∈ G.vertexSet := by
  -- Select the given edge in the endpoint union and then select the stated endpoint.
  rw [G.vertexSet_def, Set.mem_iUnion]
  refine ⟨i, ?_⟩
  rcases hx with rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

/-- Distinct edge sets intersect only at points that are endpoints of both edges. -/
theorem inter_subset_endpoints (G : FiniteLinearGraph.{u, v} X) {i j : G.Edge}
    (hij : i ≠ j) :
    G.edgeSet i ∩ G.edgeSet j ⊆
      ({G.edge i 0, G.edge i 1} ∩ {G.edge j 0, G.edge j 1} : Set X) := by
  -- The accessor unfolds to the ranges governed by the stored endpoint condition.
  exact G.interSubsetEndpoints hij

/-- The intersection of two distinct edge sets contains at most one point. -/
theorem inter_subsingleton (G : FiniteLinearGraph.{u, v} X) {i j : G.Edge}
    (hij : i ≠ j) :
    (G.edgeSet i ∩ G.edgeSet j).Subsingleton := by
  -- The accessor unfolds to the ranges governed by the stored intersection condition.
  exact G.interSubsingleton hij


end FiniteLinearGraph
