module

public import Topology_Munkres_2000.Book.Exercise_3_99_8.Subnet
public import Mathlib.Topology.Compactness.Compact

public section

universe u v

namespace Net

/-- Helper for Lemma 3.99.1: indices pairing a net index with a neighborhood
of the cluster point that contains the corresponding net value. -/
private abbrev ClusterIndex {J : Type u} {X : Type v} [Preorder J]
    [TopologicalSpace X] (net : J → X) (x : X) :=
  {p : J × OrderDual (Set X) //
    OrderDual.ofDual p.2 ∈ nhds x ∧ net p.1 ∈ OrderDual.ofDual p.2}

/-- Helper for Lemma 3.99.1: the cluster-index type is nonempty. -/
private lemma clusterIndexNonempty {J : Type u} {X : Type v} [Nonempty J]
    [Preorder J] [TopologicalSpace X] (net : J → X) (x : X) :
    Nonempty (ClusterIndex net x) := by
  -- Pair any original index with the universal neighborhood.
  obtain ⟨α⟩ := (inferInstance : Nonempty J)
  exact ⟨⟨(α, OrderDual.toDual Set.univ), Filter.univ_mem, Set.mem_univ _⟩⟩

/-- Helper for Lemma 3.99.1: cluster indices form a directed preorder when
`x` is a cluster point of the original net. -/
private lemma clusterIndexIsDirectedOrder {J : Type u} {X : Type v}
    [Nonempty J] [Preorder J] [IsDirectedOrder J] [TopologicalSpace X]
    (net : J → X) (x : X) (h : MapClusterPt x Filter.atTop net) :
    IsDirectedOrder (ClusterIndex net x) := by
  -- Bound both original indices and then hit the intersection of the stored neighborhoods.
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨N, haN, hbN⟩ := exists_ge_ge a.1.1 b.1.1
  have hinter : OrderDual.ofDual a.1.2 ∩ OrderDual.ofDual b.1.2 ∈ nhds x :=
    Filter.inter_mem a.2.1 b.2.1
  obtain ⟨n, hNn, hn⟩ :=
    (Filter.inf_map_atTop_neBot_iff.mp h) _ hinter N
  let k : ClusterIndex net x :=
    ⟨(n, OrderDual.toDual (OrderDual.ofDual a.1.2 ∩ OrderDual.ofDual b.1.2)),
      hinter, hn⟩
  -- Reverse inclusion in the second coordinate makes the intersection an upper bound.
  refine ⟨k, ?_, ?_⟩
  · exact ⟨haN.trans hNn, Set.inter_subset_left⟩
  · exact ⟨hbN.trans hNn, Set.inter_subset_right⟩

/-- Helper for Lemma 3.99.1: projecting a cluster index to its original
index is an admissible subnet reindexing. -/
private lemma clusterIndexProjectionIsSubnetMap {J : Type u} {X : Type v}
    [Preorder J] [TopologicalSpace X] (net : J → X) (x : X) :
    IsSubnetMap (fun k : ClusterIndex net x ↦ k.1.1) := by
  -- Projection preserves the product order.
  rw [isSubnetMap_iff]
  constructor
  · intro a b hab
    exact hab.1
  · intro α
    -- The universal neighborhood supplies a cluster index above every original index.
    let k : ClusterIndex net x :=
      ⟨(α, OrderDual.toDual Set.univ), Filter.univ_mem, Set.mem_univ _⟩
    exact ⟨α, ⟨k, rfl⟩, le_rfl⟩

/-- Helper for Lemma 3.99.1: the net projected along cluster indices
converges to the designated cluster point. -/
private lemma clusterIndexProjectionTendsto {J : Type u} {X : Type v}
    [Nonempty J] [Preorder J] [IsDirectedOrder J] [TopologicalSpace X]
    (net : J → X) (x : X) (h : MapClusterPt x Filter.atTop net) :
    Filter.Tendsto (net ∘ fun k : ClusterIndex net x ↦ k.1.1)
      Filter.atTop (nhds x) := by
  letI : Nonempty (ClusterIndex net x) := clusterIndexNonempty net x
  letI : IsDirectedOrder (ClusterIndex net x) :=
    clusterIndexIsDirectedOrder net x h
  -- A late hit in each neighborhood becomes a threshold in the cluster-index order.
  refine Filter.tendsto_atTop'.2 ?_
  intro U hU
  obtain ⟨N⟩ := (inferInstance : Nonempty J)
  obtain ⟨α, _, hα⟩ :=
    (Filter.inf_map_atTop_neBot_iff.mp h) U hU N
  let k : ClusterIndex net x := ⟨(α, OrderDual.toDual U), hU, hα⟩
  refine ⟨k, fun b hkb ↦ ?_⟩
  -- Later cluster indices store smaller neighborhoods, so their values remain in `U`.
  exact hkb.2 b.2.2

/-- Lemma 3.99.1: A point is a cluster point of a net exactly when some
subnet converges to it. -/
theorem mapClusterPt_iff_exists_tendsto_subnet {J : Type u} {X : Type v}
    [Nonempty J] [Preorder J] [IsDirectedOrder J] [TopologicalSpace X]
    (net : J → X) (x : X) :
    MapClusterPt x Filter.atTop net ↔
      ∃ subnet : Subnet net,
        Filter.Tendsto subnet.values Filter.atTop (nhds x) := by
  constructor
  · intro h
    letI : Nonempty (ClusterIndex net x) := clusterIndexNonempty net x
    letI : IsDirectedOrder (ClusterIndex net x) :=
      clusterIndexIsDirectedOrder net x h
    -- Package the projection and its structural facts as the required subnet.
    let subnet : Subnet net :=
      { index := ClusterIndex net x
        map := fun k ↦ k.1.1
        isSubnetMap := clusterIndexProjectionIsSubnetMap net x }
    refine ⟨subnet, ?_⟩
    -- The subnet values are exactly the projected cluster-index net.
    simpa only [Subnet.values, subnet] using
      clusterIndexProjectionTendsto net x h
  · rintro ⟨subnet, hsubnet⟩
    -- Convergence gives a cluster point on the subnet, which cofinality transports back.
    apply MapClusterPt.of_comp subnet.tendsto_map
    simpa only [Subnet.values] using hsubnet.mapClusterPt

end Net
