module

public import Mathlib.Topology.Basic

public section

universe u

namespace Topology

/-- A space covered by a finite family of closed subspaces that all contain a specified point
and meet pairwise exactly at that point. -/
class IsFiniteWedge {X : Type u} [TopologicalSpace X] {ι : Type*} [Fintype ι]
    (S : ι → Set X) (p : X) : Prop where
  /-- The subspaces cover the ambient space. -/
  covers : ⋃ i, S i = Set.univ
  /-- Every subspace is closed in the ambient space. -/
  isClosed (i : ι) : IsClosed (S i)
  /-- The specified wedge point belongs to every subspace. -/
  point_mem (i : ι) : p ∈ S i
  /-- Distinct subspaces intersect exactly at the specified point. -/
  inter_eq : Pairwise (fun i j ↦ S i ∩ S j = {p})

namespace IsFiniteWedge

variable {X : Type u} [TopologicalSpace X] {ι : Type*} [Fintype ι]
  {S : ι → Set X} {p : X}

/-- The finite-wedge property is equivalent to the source's covering, closedness,
common-point, and intersection conditions. -/
theorem iff :
    IsFiniteWedge S p ↔
      (⋃ i, S i = Set.univ) ∧ (∀ i, IsClosed (S i)) ∧
        (∀ i, p ∈ S i) ∧ Pairwise (fun i j ↦ S i ∩ S j = {p}) :=
  ⟨fun h ↦ ⟨h.covers, h.isClosed, h.point_mem, h.inter_eq⟩,
    fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- The source's defining conditions construct the finite-wedge property. -/
theorem of
    (h_cover : ⋃ i, S i = Set.univ)
    (h_closed : ∀ i, IsClosed (S i))
    (h_point : ∀ i, p ∈ S i)
    (h_inter : Pairwise (fun i j ↦ S i ∩ S j = {p})) :
    IsFiniteWedge S p :=
  ⟨h_cover, h_closed, h_point, h_inter⟩

end IsFiniteWedge

end Topology
