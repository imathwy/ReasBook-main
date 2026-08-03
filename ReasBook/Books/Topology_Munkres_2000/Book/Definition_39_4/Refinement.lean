module

public import Mathlib.Topology.Basic

public section

open Set

universe u

/-- A collection `ℬ` refines `𝒜` when every member of `ℬ` is contained in a
member of `𝒜`. -/
class IsRefinement {X : Type u} (ℬ 𝒜 : Set (Set X)) : Prop where
  subset_of_mem {B : Set X} (hB : B ∈ ℬ) : ∃ A ∈ 𝒜, B ⊆ A

/-- The defining condition for a refinement. -/
theorem isRefinement_iff {X : Type u} {ℬ 𝒜 : Set (Set X)} :
    IsRefinement ℬ 𝒜 ↔ ∀ B ∈ ℬ, ∃ A ∈ 𝒜, B ⊆ A := by
  constructor
  · exact fun h B hB ↦ h.subset_of_mem hB
  · exact fun h ↦ ⟨fun hB ↦ h _ hB⟩

namespace IsRefinement

/-- Every collection refines itself. -/
theorem refl {X : Type u} (𝒜 : Set (Set X)) : IsRefinement 𝒜 𝒜 :=
  ⟨fun hA ↦ ⟨_, hA, Subset.rfl⟩⟩

/-- Refinement is transitive. -/
theorem trans {X : Type u} {𝒞 ℬ 𝒜 : Set (Set X)}
    (h𝒞ℬ : IsRefinement 𝒞 ℬ) (hℬ𝒜 : IsRefinement ℬ 𝒜) : IsRefinement 𝒞 𝒜 := by
  constructor
  intro C hC
  obtain ⟨B, hB, hCB⟩ := h𝒞ℬ.subset_of_mem hC
  obtain ⟨A, hA, hBA⟩ := hℬ𝒜.subset_of_mem hB
  exact ⟨A, hA, hCB.trans hBA⟩

end IsRefinement

/-- An open refinement is a refinement all of whose members are open. -/
class IsOpenRefinement {X : Type u} [TopologicalSpace X]
    (ℬ 𝒜 : Set (Set X)) : Prop extends IsRefinement ℬ 𝒜 where
  isOpen_of_mem {B : Set X} (hB : B ∈ ℬ) : IsOpen B

/-- An open refinement canonically determines a refinement. -/
instance {X : Type u} [TopologicalSpace X] {ℬ 𝒜 : Set (Set X)}
    [h : IsOpenRefinement ℬ 𝒜] : IsRefinement ℬ 𝒜 := h.toIsRefinement

/-- The defining conditions for an open refinement. -/
theorem isOpenRefinement_iff {X : Type u} [TopologicalSpace X]
    {ℬ 𝒜 : Set (Set X)} :
    IsOpenRefinement ℬ 𝒜 ↔ IsRefinement ℬ 𝒜 ∧ ∀ B ∈ ℬ, IsOpen B := by
  constructor
  · exact fun h ↦ ⟨h.toIsRefinement, fun _ hB ↦ h.isOpen_of_mem hB⟩
  · rintro ⟨h_refinement, h_open⟩
    exact { h_refinement with isOpen_of_mem := fun hB ↦ h_open _ hB }

/-- A closed refinement is a refinement all of whose members are closed. -/
class IsClosedRefinement {X : Type u} [TopologicalSpace X]
    (ℬ 𝒜 : Set (Set X)) : Prop extends IsRefinement ℬ 𝒜 where
  isClosed_of_mem {B : Set X} (hB : B ∈ ℬ) : IsClosed B

/-- A closed refinement canonically determines a refinement. -/
instance {X : Type u} [TopologicalSpace X] {ℬ 𝒜 : Set (Set X)}
    [h : IsClosedRefinement ℬ 𝒜] : IsRefinement ℬ 𝒜 := h.toIsRefinement

/-- The defining conditions for a closed refinement. -/
theorem isClosedRefinement_iff {X : Type u} [TopologicalSpace X]
    {ℬ 𝒜 : Set (Set X)} :
    IsClosedRefinement ℬ 𝒜 ↔ IsRefinement ℬ 𝒜 ∧ ∀ B ∈ ℬ, IsClosed B := by
  constructor
  · exact fun h ↦ ⟨h.toIsRefinement, fun _ hB ↦ h.isClosed_of_mem hB⟩
  · rintro ⟨h_refinement, h_closed⟩
    exact { h_refinement with isClosed_of_mem := fun hB ↦ h_closed _ hB }
