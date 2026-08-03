module

public import Topology_Munkres_2000.Book.Definition_6_0_1.LocallyFinite

public section

open Set

universe u

namespace Set.LocallyFinite

/-- A subcollection of a locally finite collection is locally finite. -/
theorem mono {X : Type u} [TopologicalSpace X] {𝒜 𝓑 : Set (Set X)}
    (h𝒜 : 𝒜.LocallyFinite) (h𝓑𝒜 : 𝓑 ⊆ 𝒜) : 𝓑.LocallyFinite := by
  change _root_.LocallyFinite (Subtype.val : 𝒜 → Set X) at h𝒜
  change _root_.LocallyFinite (Subtype.val : 𝓑 → Set X)
  let inclusion : 𝓑 → 𝒜 := fun B ↦ ⟨B, h𝓑𝒜 B.property⟩
  have h_inclusion : Function.Injective inclusion := by
    intro A B h
    apply Subtype.ext
    exact congrArg (fun C : 𝒜 ↦ (C : Set X)) h
  simpa [inclusion, Function.comp_def] using h𝒜.comp_injective h_inclusion

/-- Taking the closure of every member preserves local finiteness. -/
theorem closure_image {X : Type u} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : 𝒜.LocallyFinite) : (closure '' 𝒜).LocallyFinite := by
  change _root_.LocallyFinite (Subtype.val : 𝒜 → Set X) at h𝒜
  change _root_.LocallyFinite (Subtype.val : closure '' 𝒜 → Set X)
  let toClosure : 𝒜 → closure '' 𝒜 := fun A ↦ ⟨closure A, A, A.property, rfl⟩
  have h_surjective : Function.Surjective toClosure := by
    rintro ⟨B, A, hA, rfl⟩
    exact ⟨⟨A, hA⟩, rfl⟩
  apply _root_.LocallyFinite.of_comp_surjective h_surjective
  simpa [toClosure, Function.comp_def] using h𝒜.closure

/-- Closure commutes with the union of a locally finite collection. -/
theorem closure_sUnion {X : Type u} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : 𝒜.LocallyFinite) : closure (⋃₀ 𝒜) = ⋃₀ (closure '' 𝒜) := by
  change _root_.LocallyFinite (Subtype.val : 𝒜 → Set X) at h𝒜
  rw [sUnion_image]
  simpa only [sUnion_eq_iUnion, iUnion_subtype] using h𝒜.closure_iUnion

end Set.LocallyFinite
