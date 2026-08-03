module

public import Topology_Munkres_2000.Book.Definition_61_2.Arc

public section

open Set

universe u v

namespace Topology.ArcFamily

/-- Two distinct arcs meet in at most one point, and every such common point is an
endpoint of both arcs. -/
def MeetAtEndpoints {X : Type u} {ι : Type v} [TopologicalSpace X]
    (A : ι → Set X) [∀ i, Topology.IsArc (A i)] : Prop :=
  Pairwise fun i j ↦
    (A i ∩ A j).Subsingleton ∧
      ∀ x (hxi : x ∈ A i) (hxj : x ∈ A j),
          Topology.IsArc.IsEndpoint (⟨x, hxi⟩ : A i) ∧
          Topology.IsArc.IsEndpoint (⟨x, hxj⟩ : A j)

/-- Helper for Exercise 64.1: pairwise subsingleton intersections whose common points
are endpoints determine an endpoint-meeting family of arcs. -/
theorem meetAtEndpoints_of {X : Type u} {ι : Type v} [TopologicalSpace X]
    (A : ι → Set X) [∀ i, Topology.IsArc (A i)]
    (h_inter : ∀ {i j}, i ≠ j → (A i ∩ A j).Subsingleton)
    (h_endpoint : ∀ {i j}, i ≠ j → ∀ x (hxi : x ∈ A i) (hxj : x ∈ A j),
      Topology.IsArc.IsEndpoint (⟨x, hxi⟩ : A i) ∧
        Topology.IsArc.IsEndpoint (⟨x, hxj⟩ : A j)) :
    MeetAtEndpoints A := by
  -- Assemble the two defining properties for each pair of distinct indices.
  intro i j hij
  exact ⟨h_inter hij, h_endpoint hij⟩

/-- Distinct arcs in an endpoint-meeting family have subsingleton intersection. -/
theorem inter_subsingleton {X : Type u} {ι : Type v} [TopologicalSpace X]
    (A : ι → Set X) [∀ i, Topology.IsArc (A i)] (hA : MeetAtEndpoints A)
    {i j : ι} (hij : i ≠ j) :
    (A i ∩ A j).Subsingleton :=
  (hA hij).1

/-- A common point of distinct arcs in an endpoint-meeting family is an endpoint
of both arcs. -/
theorem isEndpoint {X : Type u} {ι : Type v} [TopologicalSpace X]
    (A : ι → Set X) [∀ i, Topology.IsArc (A i)] (hA : MeetAtEndpoints A)
    {i j : ι} (hij : i ≠ j) (x : X) (hxi : x ∈ A i) (hxj : x ∈ A j) :
    Topology.IsArc.IsEndpoint (⟨x, hxi⟩ : A i) ∧
      Topology.IsArc.IsEndpoint (⟨x, hxj⟩ : A j) :=
  (hA hij).2 x hxi hxj

end Topology.ArcFamily
