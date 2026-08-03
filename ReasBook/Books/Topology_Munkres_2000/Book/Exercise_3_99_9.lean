module

public import Topology_Munkres_2000.Book.Lemma_3_99_1.ClusterPoint

public section

universe u v

/- Exercise 3.99.9: The accumulation-point condition for a net is the canonical
predicate `MapClusterPt x Filter.atTop net`. -/
#check fun {J : Type u} {X : Type v} [Nonempty J] [Preorder J]
    [IsDirectedOrder J] [TopologicalSpace X] (net : J → X) (x : X) ↦
  MapClusterPt x Filter.atTop net

namespace Net

/-- A point is an accumulation point of a net exactly when the indices where
the net lies in each neighborhood form a cofinal set. -/
theorem mapClusterPt_atTop_iff_isCofinal {J : Type u} {X : Type v}
    [Nonempty J] [Preorder J] [IsDirectedOrder J] [TopologicalSpace X]
    (net : J → X) (x : X) :
    MapClusterPt x Filter.atTop net ↔
      ∀ U ∈ nhds x, IsCofinal {α | net α ∈ U} := by
  rw [mapClusterPt_iff_frequently]
  constructor
  · intro h U hU α
    obtain ⟨β, hαβ, hβ⟩ := Filter.frequently_atTop.mp (h U hU) α
    exact ⟨β, hβ, hαβ⟩
  · intro h U hU
    rw [Filter.frequently_atTop]
    intro α
    obtain ⟨β, hβ, hαβ⟩ := h U hU α
    exact ⟨β, hαβ, hβ⟩

end Net

/- A net has `x` as an accumulation point if and only if some subnet converges
to `x`. -/
#check fun {J : Type u} {X : Type v} [Nonempty J] [Preorder J]
    [IsDirectedOrder J] [TopologicalSpace X] (net : J → X) (x : X) ↦
  Net.mapClusterPt_iff_exists_tendsto_subnet net x
