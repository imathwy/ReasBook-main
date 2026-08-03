module

public import Topology_Munkres_2000.Book.Definition_39_4.Refinement

public section

open Set

universe u

/-- A barycentric refinement is an open refinement covering the space such that
the union of any two intersecting members lies in one member of the original family. -/
class IsBarycentricRefinement {X : Type u} [TopologicalSpace X]
    (ℬ 𝒜 : Set (Set X)) : Prop extends IsOpenRefinement ℬ 𝒜 where
  sUnion_eq_univ : ⋃₀ ℬ = Set.univ
  union_subset_of_inter_nonempty {B B' : Set X} (hB : B ∈ ℬ) (hB' : B' ∈ ℬ)
      (h_inter : (B ∩ B').Nonempty) : ∃ A ∈ 𝒜, B ∪ B' ⊆ A

/-- A barycentric refinement canonically determines an open refinement. -/
instance IsBarycentricRefinement.instIsOpenRefinement
    {X : Type u} [TopologicalSpace X] {ℬ 𝒜 : Set (Set X)}
    [h : IsBarycentricRefinement ℬ 𝒜] : IsOpenRefinement ℬ 𝒜 := h.toIsOpenRefinement

/-- The defining conditions for a barycentric refinement. -/
theorem isBarycentricRefinement_iff {X : Type u} [TopologicalSpace X]
    {ℬ 𝒜 : Set (Set X)} :
    IsBarycentricRefinement ℬ 𝒜 ↔
      IsOpenRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧
        ∀ B ∈ ℬ, ∀ B' ∈ ℬ, (B ∩ B').Nonempty → ∃ A ∈ 𝒜, B ∪ B' ⊆ A := by
  constructor
  · intro h
    exact ⟨h.toIsOpenRefinement, h.sUnion_eq_univ,
      fun B hB B' hB' h_inter ↦ h.union_subset_of_inter_nonempty hB hB' h_inter⟩
  · rintro ⟨h_refinement, h_cover, h_union⟩
    exact { h_refinement with
      sUnion_eq_univ := h_cover
      union_subset_of_inter_nonempty := fun hB hB' h_inter ↦ h_union _ hB _ hB' h_inter }
