module

public import Mathlib.Analysis.Complex.Circle

public section

universe u v

namespace Topology

/-- A family of subspaces homeomorphic to `Circle` that covers the ambient space and whose
 distinct members meet exactly at a specified point. -/
class IsCircleUnion {ι : Type v} {X : Type u} [TopologicalSpace X]
    (S : ι → Set X) (p : X) : Prop where
  /-- The circles cover the ambient space. -/
  covers : ⋃ i, S i = Set.univ
  /-- Every member of the family is homeomorphic to the unit circle. -/
  homeomorphic_circle (i : ι) : Nonempty (S i ≃ₜ Circle)
  /-- Distinct members of the family intersect exactly at the specified point. -/
  inter_eq : Pairwise (fun i j ↦ S i ∩ S j = {p})

namespace IsCircleUnion

variable {ι : Type v} {X : Type u} [TopologicalSpace X] {S : ι → Set X} {p : X}

/-- The circle-union property is equivalent to its covering, circle, and intersection
conditions. -/
theorem iff :
    IsCircleUnion S p ↔
      (⋃ i, S i = Set.univ) ∧
        (∀ i, Nonempty (S i ≃ₜ Circle)) ∧ Pairwise (fun i j ↦ S i ∩ S j = {p}) :=
  ⟨fun h ↦ ⟨h.covers, h.homeomorphic_circle, h.inter_eq⟩,
    fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

/-- The source's covering, circle, and intersection conditions construct a circle union. -/
theorem of
    (h_cover : ⋃ i, S i = Set.univ)
    (h_circle : ∀ i, Nonempty (S i ≃ₜ Circle))
    (h_inter : Pairwise (fun i j ↦ S i ∩ S j = {p})) :
    IsCircleUnion S p :=
  ⟨h_cover, h_circle, h_inter⟩

end IsCircleUnion

end Topology

end
