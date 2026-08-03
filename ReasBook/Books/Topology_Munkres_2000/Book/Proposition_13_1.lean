module

public import Mathlib.Topology.Bases

public section

open Set

namespace TopologicalSpace

/-- Proposition 13.1. A family satisfying the two basis axioms is a basis for
the topology it generates: its open sets are exactly those from Munkres'
pointwise definition. -/
theorem isOpen_generateFrom_iff_of_basis {X : Type*} {𝓑 : Set (Set X)}
    (h_cover : ∀ x, ∃ B ∈ 𝓑, x ∈ B)
    (h_inter : ∀ B₁ ∈ 𝓑, ∀ B₂ ∈ 𝓑, ∀ x ∈ B₁ ∩ B₂,
      ∃ B₃ ∈ 𝓑, x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂) (U : Set X) :
    (generateFrom 𝓑).IsOpen U ↔
      ∀ x ∈ U, ∃ B ∈ 𝓑, x ∈ B ∧ B ⊆ U := by
  constructor
  · intro hU
    induction hU with
    | basic V hV =>
        exact fun x hx ↦ ⟨V, hV, hx, Subset.rfl⟩
    | univ =>
        exact fun x _ ↦ by
          obtain ⟨B, hB, hxB⟩ := h_cover x
          exact ⟨B, hB, hxB, subset_univ B⟩
    | inter V W _ _ hV hW =>
        intro x hx
        obtain ⟨B₁, hB₁, hxB₁, hB₁V⟩ := hV x hx.1
        obtain ⟨B₂, hB₂, hxB₂, hB₂W⟩ := hW x hx.2
        obtain ⟨B₃, hB₃, hxB₃, hB₃sub⟩ :=
          h_inter B₁ hB₁ B₂ hB₂ x ⟨hxB₁, hxB₂⟩
        exact ⟨B₃, hB₃, hxB₃, hB₃sub.trans (inter_subset_inter hB₁V hB₂W)⟩
    | sUnion S _ hS =>
        intro x hx
        obtain ⟨V, hVS, hxV⟩ := mem_sUnion.1 hx
        obtain ⟨B, hB, hxB, hBV⟩ := hS V hVS x hxV
        exact ⟨B, hB, hxB, hBV.trans (subset_sUnion_of_mem hVS)⟩
  · intro hU
    rw [show U = ⋃₀ {B | B ∈ 𝓑 ∧ B ⊆ U} by
      ext x
      constructor
      · intro hx
        obtain ⟨B, hB, hxB, hBU⟩ := hU x hx
        exact mem_sUnion_of_mem hxB ⟨hB, hBU⟩
      · intro hx
        obtain ⟨B, ⟨_, hBU⟩, hxB⟩ := mem_sUnion.1 hx
        exact hBU hxB]
    exact .sUnion _ fun B hB ↦ .basic B hB.1

end TopologicalSpace
