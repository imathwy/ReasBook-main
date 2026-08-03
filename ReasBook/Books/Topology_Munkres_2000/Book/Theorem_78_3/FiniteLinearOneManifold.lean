module

public import Topology_Munkres_2000.Book.Example_50_6.LinearGraph
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Geometry.Manifold.Instances.Real

open scoped Manifold

public section

universe u v

namespace FiniteLinearGraph

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Theorem 78.3: the geometric endpoint vertices of a finite linear graph. -/
abbrev Endpoint (G : FiniteLinearGraph.{u, v} X) := G.vertexSet

/-- Helper for Theorem 78.3: the initial endpoint of a parameterized edge. -/
def edgeStart (G : FiniteLinearGraph.{u, v} X) (i : G.Edge) : G.Endpoint :=
  ⟨G.edge i 0, G.endpoint_mem_vertexSet i 0 (Or.inl rfl)⟩

/-- Helper for Theorem 78.3: the terminal endpoint of a parameterized edge. -/
def edgeEnd (G : FiniteLinearGraph.{u, v} X) (i : G.Edge) : G.Endpoint :=
  ⟨G.edge i 1, G.endpoint_mem_vertexSet i 1 (Or.inr rfl)⟩

/-- Helper for Theorem 78.3: the two endpoints of an embedded edge are distinct. -/
theorem edgeStart_ne_edgeEnd (G : FiniteLinearGraph.{u, v} X) (i : G.Edge) :
    G.edgeStart i ≠ G.edgeEnd i := by
  -- Equality of endpoint vertices would contradict injectivity of the edge embedding.
  intro h
  have hparameter : (0 : unitInterval) = 1 :=
    (G.edgeEmbedding i).injective (congrArg Subtype.val h)
  exact zero_ne_one hparameter

/-- Helper for Theorem 78.3: two parameterized edges with the same ordered
endpoints are the same edge. -/
theorem edge_eq_of_edgeStart_eq_of_edgeEnd_eq
    (G : FiniteLinearGraph.{u, v} X) {i j : G.Edge}
    (hstart : G.edgeStart i = G.edgeStart j)
    (hend : G.edgeEnd i = G.edgeEnd j) : i = j := by
  -- If the indices differed, both distinct endpoints would lie in their
  -- subsingleton intersection.
  by_contra hij
  have hstartValue : G.edge i 0 = G.edge j 0 := congrArg Subtype.val hstart
  have hendValue : G.edge i 1 = G.edge j 1 := congrArg Subtype.val hend
  have hzero : G.edge i 0 ∈ G.edgeSet i ∩ G.edgeSet j :=
    ⟨⟨0, rfl⟩, ⟨0, hstartValue.symm⟩⟩
  have hone : G.edge i 1 ∈ G.edgeSet i ∩ G.edgeSet j :=
    ⟨⟨1, rfl⟩, ⟨1, hendValue.symm⟩⟩
  have hendpoint : G.edge i 0 = G.edge i 1 :=
    G.inter_subsingleton hij hzero hone
  have hparameter : (0 : unitInterval) = 1 :=
    (G.edgeEmbedding i).injective hendpoint
  exact zero_ne_one hparameter

/-- Helper for Theorem 78.3: distinct parameterized edges cannot have the
same two endpoints in opposite orders. -/
theorem edge_eq_of_edgeStart_eq_edgeEnd_of_edgeEnd_eq_edgeStart
    (G : FiniteLinearGraph.{u, v} X) {i j : G.Edge}
    (hstart : G.edgeStart i = G.edgeEnd j)
    (hend : G.edgeEnd i = G.edgeStart j) : i = j := by
  -- If the indices differed, both endpoint values would lie in their
  -- subsingleton intersection, even though one embedded edge separates them.
  by_contra hij
  have hstartValue : G.edge i 0 = G.edge j 1 := congrArg Subtype.val hstart
  have hendValue : G.edge i 1 = G.edge j 0 := congrArg Subtype.val hend
  have hzero : G.edge i 0 ∈ G.edgeSet i ∩ G.edgeSet j :=
    ⟨⟨0, rfl⟩, ⟨1, hstartValue.symm⟩⟩
  have hone : G.edge i 1 ∈ G.edgeSet i ∩ G.edgeSet j :=
    ⟨⟨1, rfl⟩, ⟨0, hendValue.symm⟩⟩
  have hendpoint : G.edge i 0 = G.edge i 1 :=
    G.inter_subsingleton hij hzero hone
  have hparameter : (0 : unitInterval) = 1 :=
    (G.edgeEmbedding i).injective hendpoint
  exact zero_ne_one hparameter

/-- Helper for Theorem 78.3: the simple graph whose edges are the endpoint pairs
of the parameterized intervals. -/
def endpointIncidenceGraph (G : FiniteLinearGraph.{u, v} X) :
    SimpleGraph G.Endpoint :=
  SimpleGraph.fromRel fun x y ↦
    ∃ i : G.Edge, x = G.edgeStart i ∧ y = G.edgeEnd i

/-- Helper for Theorem 78.3: incidence-graph adjacency means that the two
vertices are the endpoints of one parameterized edge, in either order. -/
theorem endpointIncidenceGraph_adj (G : FiniteLinearGraph.{u, v} X)
    (x y : G.Endpoint) :
    G.endpointIncidenceGraph.Adj x y ↔
      ∃ i : G.Edge,
        (x = G.edgeStart i ∧ y = G.edgeEnd i) ∨
          (x = G.edgeEnd i ∧ y = G.edgeStart i) := by
  -- Unfold `fromRel`; its second disjunct supplies the reversed orientation.
  rw [endpointIncidenceGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, ⟨i, hxi, hyi⟩ | ⟨i, hyi, hxi⟩⟩
    · exact ⟨i, Or.inl ⟨hxi, hyi⟩⟩
    · exact ⟨i, Or.inr ⟨hxi, hyi⟩⟩
  · rintro ⟨i, ⟨hxi, hyi⟩ | ⟨hxi, hyi⟩⟩
    · refine ⟨?_, Or.inl ⟨i, hxi, hyi⟩⟩
      rw [hxi, hyi]
      exact G.edgeStart_ne_edgeEnd i
    · refine ⟨?_, Or.inr ⟨i, hyi, hxi⟩⟩
      rw [hxi, hyi]
      exact (G.edgeStart_ne_edgeEnd i).symm

/-- Helper for Theorem 78.3: the edges incident to one geometric endpoint. -/
abbrev IncidentEdgeAt (G : FiniteLinearGraph.{u, v} X) (x : G.Endpoint) :=
  {i : G.Edge // x = G.edgeStart i ∨ x = G.edgeEnd i}

/-- Helper for Theorem 78.3: the endpoint opposite `x` along an incident edge. -/
noncomputable def incidentEdgeOpposite (G : FiniteLinearGraph.{u, v} X)
    (x : G.Endpoint) (i : G.IncidentEdgeAt x) : G.Endpoint :=
  @ite G.Endpoint (x = G.edgeStart i.1)
    (Classical.decEq G.Endpoint x (G.edgeStart i.1))
      (G.edgeEnd i.1) (G.edgeStart i.1)

/-- Helper for Theorem 78.3: when an incident edge starts at `x`, its opposite
endpoint is its terminal endpoint. -/
theorem incidentEdgeOpposite_eq_edgeEnd_of_eq_edgeStart
    (G : FiniteLinearGraph.{u, v} X) (x : G.Endpoint)
    (i : G.IncidentEdgeAt x) (hstart : x = G.edgeStart i.1) :
    G.incidentEdgeOpposite x i = G.edgeEnd i.1 := by
  -- Select the starting-endpoint branch of the definition.
  rw [incidentEdgeOpposite, if_pos hstart]

/-- Helper for Theorem 78.3: when an incident edge ends at `x`, its opposite
endpoint is its initial endpoint. -/
theorem incidentEdgeOpposite_eq_edgeStart_of_eq_edgeEnd
    (G : FiniteLinearGraph.{u, v} X) (x : G.Endpoint)
    (i : G.IncidentEdgeAt x) (hend : x = G.edgeEnd i.1) :
    G.incidentEdgeOpposite x i = G.edgeStart i.1 := by
  -- The two embedded endpoints are distinct, so the terminal incidence forces
  -- the second branch of the definition.
  have hnotStart : x ≠ G.edgeStart i.1 := by
    intro hstart
    exact G.edgeStart_ne_edgeEnd i.1 (hstart.symm.trans hend)
  rw [incidentEdgeOpposite, if_neg hnotStart]

/-- Helper for Theorem 78.3: the opposite endpoint of an incident edge is
adjacent to `x` in the endpoint-incidence graph. -/
theorem incidentEdgeOpposite_adj (G : FiniteLinearGraph.{u, v} X)
    (x : G.Endpoint) (i : G.IncidentEdgeAt x) :
    G.endpointIncidenceGraph.Adj x (G.incidentEdgeOpposite x i) := by
  -- Orient the adjacency witness according to which endpoint equals `x`.
  rcases i.2 with hstart | hend
  · rw [G.incidentEdgeOpposite_eq_edgeEnd_of_eq_edgeStart x i hstart]
    exact (G.endpointIncidenceGraph_adj x (G.edgeEnd i.1)).mpr
      ⟨i.1, Or.inl ⟨hstart, rfl⟩⟩
  · rw [G.incidentEdgeOpposite_eq_edgeStart_of_eq_edgeEnd x i hend]
    exact (G.endpointIncidenceGraph_adj x (G.edgeStart i.1)).mpr
      ⟨i.1, Or.inr ⟨hend, rfl⟩⟩

/-- Helper for Theorem 78.3: two incident edges with the same opposite endpoint
are equal, including when their stored interval orientations differ. -/
theorem incidentEdgeOpposite_injective (G : FiniteLinearGraph.{u, v} X)
    (x : G.Endpoint) : Function.Injective (G.incidentEdgeOpposite x) := by
  intro i j hopposite
  apply Subtype.ext
  rcases i.2 with hiStart | hiEnd
  · rcases j.2 with hjStart | hjEnd
    · apply G.edge_eq_of_edgeStart_eq_of_edgeEnd_eq
      · exact hiStart.symm.trans hjStart
      · calc
          G.edgeEnd i.1 = G.incidentEdgeOpposite x i :=
            (G.incidentEdgeOpposite_eq_edgeEnd_of_eq_edgeStart x i hiStart).symm
          _ = G.incidentEdgeOpposite x j := hopposite
          _ = G.edgeEnd j.1 :=
            G.incidentEdgeOpposite_eq_edgeEnd_of_eq_edgeStart x j hjStart
    · apply G.edge_eq_of_edgeStart_eq_edgeEnd_of_edgeEnd_eq_edgeStart
      · exact hiStart.symm.trans hjEnd
      · calc
          G.edgeEnd i.1 = G.incidentEdgeOpposite x i :=
            (G.incidentEdgeOpposite_eq_edgeEnd_of_eq_edgeStart x i hiStart).symm
          _ = G.incidentEdgeOpposite x j := hopposite
          _ = G.edgeStart j.1 :=
            G.incidentEdgeOpposite_eq_edgeStart_of_eq_edgeEnd x j hjEnd
  · rcases j.2 with hjStart | hjEnd
    · apply G.edge_eq_of_edgeStart_eq_edgeEnd_of_edgeEnd_eq_edgeStart
      · calc
          G.edgeStart i.1 = G.incidentEdgeOpposite x i :=
            (G.incidentEdgeOpposite_eq_edgeStart_of_eq_edgeEnd x i hiEnd).symm
          _ = G.incidentEdgeOpposite x j := hopposite
          _ = G.edgeEnd j.1 :=
            G.incidentEdgeOpposite_eq_edgeEnd_of_eq_edgeStart x j hjStart
      · exact hiEnd.symm.trans hjStart
    · apply G.edge_eq_of_edgeStart_eq_of_edgeEnd_eq
      · calc
          G.edgeStart i.1 = G.incidentEdgeOpposite x i :=
            (G.incidentEdgeOpposite_eq_edgeStart_of_eq_edgeEnd x i hiEnd).symm
          _ = G.incidentEdgeOpposite x j := hopposite
          _ = G.edgeStart j.1 :=
            G.incidentEdgeOpposite_eq_edgeStart_of_eq_edgeEnd x j hjEnd
      · exact hiEnd.symm.trans hjEnd

/-- Helper for Theorem 78.3: send an incident edge to its opposite endpoint,
regarded as a neighbor of `x`. -/
noncomputable def incidentEdgeToNeighbor (G : FiniteLinearGraph.{u, v} X)
    (x : G.Endpoint) (i : G.IncidentEdgeAt x) :
    G.endpointIncidenceGraph.neighborSet x :=
  ⟨G.incidentEdgeOpposite x i, G.incidentEdgeOpposite_adj x i⟩

/-- Helper for Theorem 78.3: every graph neighbor is the endpoint opposite
`x` on a unique incident edge. -/
theorem incidentEdgeToNeighbor_bijective (G : FiniteLinearGraph.{u, v} X)
    (x : G.Endpoint) : Function.Bijective (G.incidentEdgeToNeighbor x) := by
  -- Injectivity is the geometric fact that two distinct edges cannot share
  -- both endpoints.
  constructor
  · intro i j hij
    apply G.incidentEdgeOpposite_injective x
    exact congrArg Subtype.val hij
  · -- Surjectivity follows by unpacking the adjacency witness in either order.
    intro y
    obtain ⟨i, ⟨hstart, hyEnd⟩ | ⟨hend, hyStart⟩⟩ :=
      (G.endpointIncidenceGraph_adj x y.1).mp y.2
    · let incident : G.IncidentEdgeAt x := ⟨i, Or.inl hstart⟩
      refine ⟨incident, ?_⟩
      apply Subtype.ext
      calc
        G.incidentEdgeOpposite x incident = G.edgeEnd i :=
          G.incidentEdgeOpposite_eq_edgeEnd_of_eq_edgeStart x incident hstart
        _ = y.1 := hyEnd.symm
    · let incident : G.IncidentEdgeAt x := ⟨i, Or.inr hend⟩
      refine ⟨incident, ?_⟩
      apply Subtype.ext
      calc
        G.incidentEdgeOpposite x incident = G.edgeStart i :=
          G.incidentEdgeOpposite_eq_edgeStart_of_eq_edgeEnd x incident hend
        _ = y.1 := hyStart.symm

/-- Helper for Theorem 78.3: incident edges at `x` are canonically equivalent
to the neighbor set of `x`. -/
noncomputable def incidentEdgeEquivNeighborSet
    (G : FiniteLinearGraph.{u, v} X) (x : G.Endpoint) :
    G.IncidentEdgeAt x ≃ G.endpointIncidenceGraph.neighborSet x :=
  Equiv.ofBijective (G.incidentEdgeToNeighbor x)
    (G.incidentEdgeToNeighbor_bijective x)

/-- Helper for Theorem 78.3: graph valence is the cardinality of the incident
edge type, so the topological and combinatorial counts have the same normal form. -/
theorem endpointIncidenceGraph_neighborSet_ncard_eq_natCard_incidentEdge
    (G : FiniteLinearGraph.{u, v} X) (x : G.Endpoint) :
    (G.endpointIncidenceGraph.neighborSet x).ncard =
      Nat.card (G.IncidentEdgeAt x) := by
  -- Rewrite set cardinality as subtype cardinality and transport it through
  -- the explicit incidence equivalence.
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr (G.incidentEdgeEquivNeighborSet x).symm

/-- Helper for Theorem 78.3: two topological incident germs imply graph
valence two through the incidence equivalence. -/
theorem endpointIncidenceGraph_neighborSet_ncard_eq_two_of_incidentEdge_equiv
    (G : FiniteLinearGraph.{u, v} X) (x : G.Endpoint)
    (hincident : Nonempty (G.IncidentEdgeAt x ≃ Fin 2)) :
    (G.endpointIncidenceGraph.neighborSet x).ncard = 2 := by
  -- Count the incident-edge type through the supplied two-germ coordinates.
  rw [G.endpointIncidenceGraph_neighborSet_ncard_eq_natCard_incidentEdge x]
  obtain ⟨e⟩ := hincident
  rw [Nat.card_congr e, Nat.card_fin]

/-- Helper for Theorem 78.3: every geometric endpoint is one of the two
endpoints of a parameterized edge. -/
theorem exists_edgeStart_or_edgeEnd_eq
    (G : FiniteLinearGraph.{u, v} X) (x : G.Endpoint) :
    ∃ i : G.Edge, x = G.edgeStart i ∨ x = G.edgeEnd i := by
  -- Membership in the endpoint union selects an edge and one of its endpoints.
  have hx : (x : X) ∈ G.vertexSet := x.property
  rw [G.vertexSet_def, Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  refine ⟨i, ?_⟩
  rcases hi with hi | hi
  · exact Or.inl (Subtype.ext hi)
  · exact Or.inr (Subtype.ext hi)

/-- Helper for Theorem 78.3: every endpoint vertex has at least one neighbor. -/
theorem endpointIncidenceGraph_neighborSet_nonempty
    (G : FiniteLinearGraph.{u, v} X) (x : G.Endpoint) :
    (G.endpointIncidenceGraph.neighborSet x).Nonempty := by
  -- Use the opposite endpoint of an edge witnessing that `x` is a vertex.
  obtain ⟨i, hstart | hend⟩ := G.exists_edgeStart_or_edgeEnd_eq x
  · refine ⟨G.edgeEnd i, ?_⟩
    exact (G.endpointIncidenceGraph_adj x (G.edgeEnd i)).mpr
      ⟨i, Or.inl ⟨hstart, rfl⟩⟩
  · refine ⟨G.edgeStart i, ?_⟩
    exact (G.endpointIncidenceGraph_adj x (G.edgeStart i)).mpr
      ⟨i, Or.inr ⟨hend, rfl⟩⟩

/-- Helper for Theorem 78.3: the endpoint vertex type of a finite linear graph
is finite. -/
theorem endpoint_finite (G : FiniteLinearGraph.{u, v} X) : Finite G.Endpoint := by
  -- Local instance justification (stored edge finiteness): the graph structure
  -- carries finiteness as a field rather than as an ambient typeclass instance.
  letI : Finite G.Edge := G.edgeFinite
  -- A finite union of two-point endpoint sets is finite.
  exact (Set.finite_iUnion fun i ↦ Set.toFinite {G.edge i 0, G.edge i 1}).to_subtype

/-- Helper for Theorem 78.3: the neighbor set of every endpoint vertex is finite. -/
theorem endpointIncidenceGraph_neighborSet_finite
    (G : FiniteLinearGraph.{u, v} X) (x : G.Endpoint) :
    (G.endpointIncidenceGraph.neighborSet x).Finite := by
  -- Local instance justification (proved endpoint finiteness): this finite
  -- carrier is needed only to discharge the neighbor-set side condition.
  letI : Finite G.Endpoint := G.endpoint_finite
  exact Set.toFinite _

/-- Helper for Theorem 78.3: every endpoint vertex has positive finite degree. -/
theorem endpointIncidenceGraph_neighborSet_ncard_pos
    (G : FiniteLinearGraph.{u, v} X) (x : G.Endpoint) :
    0 < (G.endpointIncidenceGraph.neighborSet x).ncard := by
  -- Convert the explicit opposite-endpoint neighbor into positivity of `ncard`.
  rw [Set.ncard_pos (G.endpointIncidenceGraph_neighborSet_finite x)]
  exact G.endpointIncidenceGraph_neighborSet_nonempty x

/-- Helper for Theorem 78.3: because every endpoint has a neighbor, the cycle
condition is equivalent to exact valence two at every endpoint. -/
theorem endpointIncidenceGraph_isCycles_iff
    (G : FiniteLinearGraph.{u, v} X) :
    G.endpointIncidenceGraph.IsCycles ↔
      ∀ x : G.Endpoint,
        (G.endpointIncidenceGraph.neighborSet x).ncard = 2 := by
  -- The nonempty-neighborhood premise in `IsCycles` is automatic here.
  constructor
  · intro hcycles x
    exact hcycles (G.endpointIncidenceGraph_neighborSet_nonempty x)
  · intro hvalence x _
    exact hvalence x

/-- Helper for Theorem 78.3: in a finite linear presentation of a topological
one-manifold, every geometric endpoint has exactly two adjacent endpoints. -/
theorem endpointIncidenceGraph_neighborSet_ncard_eq_two
    (G : FiniteLinearGraph.{u, v} X)
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) X]
    [IsManifold (𝓡 1) 0 X] (x : G.Endpoint) :
    (G.endpointIncidenceGraph.neighborSet x).ncard = 2 := by
  -- The combinatorial transport is now complete; it remains only to classify
  -- the incident germs by the two punctured sides of a shrunken real chart.
  apply G.endpointIncidenceGraph_neighborSet_ncard_eq_two_of_incidentEdge_equiv x
  -- TODO: shrink a real chart at `x` away from every nonincident compact edge,
  -- then map incident germs to the left and right components of that chart.
  sorry

end FiniteLinearGraph
