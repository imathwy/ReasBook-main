module

public import Topology_Munkres_2000.Book.Definition_71_2.FiniteWedge
public import Mathlib.Topology.Coherent

public section

universe u v

namespace Topology

/-- A topological space is a wedge of an indexed family of circles at a common point. -/
class IsWedgeOfCircles {J : outParam (Type v)} {X : Type u} [TopologicalSpace X]
    (S : outParam (J → Set X)) (p : X) : Prop where
  /-- The indexed circles cover the ambient space. -/
  covers : ⋃ α, S α = Set.univ
  /-- Every indexed subspace is homeomorphic to the unit circle. -/
  homeomorphic_circle (α : J) : Nonempty (S α ≃ₜ Circle)
  /-- Distinct indexed circles intersect exactly at the common point. -/
  inter_eq : Pairwise (fun α β ↦ S α ∩ S β = {p})
  /-- The ambient topology is coherent with the indexed circles. -/
  isCoherentWith : Topology.IsCoherentWith (Set.range S)

namespace IsWedgeOfCircles

variable {J : Type v} {X : Type u} [TopologicalSpace X] {S : J → Set X} {p : X}

/-- The wedge-of-circles property is equivalent to the source's covering, circle,
intersection, and coherence conditions. -/
theorem iff :
    IsWedgeOfCircles S p ↔
      (⋃ α, S α = Set.univ) ∧ (∀ α, Nonempty (S α ≃ₜ Circle)) ∧
        Pairwise (fun α β ↦ S α ∩ S β = {p}) ∧ IsCoherentWith (Set.range S) :=
  ⟨fun h ↦ ⟨h.covers, h.homeomorphic_circle, h.inter_eq, h.isCoherentWith⟩,
    fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- The source's four defining conditions construct the wedge-of-circles property. -/
theorem of
    (h_cover : ⋃ α, S α = Set.univ)
    (h_circle : ∀ α, Nonempty (S α ≃ₜ Circle))
    (h_inter : Pairwise (fun α β ↦ S α ∩ S β = {p}))
    (h_coherent : IsCoherentWith (Set.range S)) :
    IsWedgeOfCircles S p :=
  ⟨h_cover, h_circle, h_inter, h_coherent⟩

/-- Every finite Hausdorff wedge of circles is a wedge of circles with coherent topology. -/
theorem ofFinite [Fintype J] (h : IsFiniteWedgeOfCircles S p) : IsWedgeOfCircles S p where
  covers := h.covers
  homeomorphic_circle := h.homeomorphic_circle
  inter_eq := h.inter_eq
  isCoherentWith := IsFiniteWedgeOfCircles.isCoherentWith h

/-- The common point of a wedge of circles belongs to every indexed circle. -/
theorem mem_basepoint [IsWedgeOfCircles S p] (α : J) : p ∈ S α := by
  -- First use the covering condition to place the basepoint in some indexed circle.
  have hp_union : p ∈ ⋃ β, S β := by
    rw [IsWedgeOfCircles.covers (S := S) (p := p)]
    exact Set.mem_univ p
  obtain ⟨β, hpβ⟩ := Set.mem_iUnion.mp hp_union
  rcases eq_or_ne β α with hβα | hβα
  · -- If the covering circle is the requested one, transport membership along the index equality.
    rwa [hβα] at hpβ
  · -- Otherwise the intersection condition puts the basepoint in both distinct circles.
    have hp_inter : p ∈ S β ∩ S α := by
      rw [IsWedgeOfCircles.inter_eq (S := S) (p := p) hβα]
      exact Set.mem_singleton p
    exact hp_inter.2

end IsWedgeOfCircles

end Topology
