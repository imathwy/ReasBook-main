module

public import Topology_Munkres_2000.Book.Definition_15_1
public import Topology_Munkres_2000.Book.Definition_15_2

public section

open Set

universe u v

namespace TopologicalSpace

/-- The family of preimages of open sets under the two projections from `X × Y`. -/
def prodSubbasis (X : Type u) (Y : Type v) [TopologicalSpace X]
    [TopologicalSpace Y] : Set (Set (X × Y)) :=
  preimage π₁ '' {U : Set X | IsOpen U} ∪ preimage π₂ '' {V : Set Y | IsOpen V}

/-- The preimage under `π₁` of an open set belongs to the projection subbasis. -/
lemma fst_preimage_mem_prodSubbasis {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {U : Set X} (hU : IsOpen U) :
    π₁ ⁻¹' U ∈ prodSubbasis X Y := by
  exact mem_union_left _ ⟨U, hU, rfl⟩

/-- The preimage under `π₂` of an open set belongs to the projection subbasis. -/
lemma snd_preimage_mem_prodSubbasis {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {V : Set Y} (hV : IsOpen V) :
    π₂ ⁻¹' V ∈ prodSubbasis X Y := by
  exact mem_union_right _ ⟨V, hV, rfl⟩

/-- A set belongs to `prodSubbasis X Y` exactly when it is the preimage of
an open set under one of the two projections. -/
lemma mem_prodSubbasis {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {s : Set (X × Y)} :
    s ∈ prodSubbasis X Y ↔
      (∃ U, IsOpen U ∧ s = π₁ ⁻¹' U) ∨ ∃ V, IsOpen V ∧ s = π₂ ⁻¹' V := by
  simp only [prodSubbasis, mem_union, mem_image]
  constructor
  · rintro (⟨U, hU, rfl⟩ | ⟨V, hV, rfl⟩)
    · exact Or.inl ⟨U, hU, rfl⟩
    · exact Or.inr ⟨V, hV, rfl⟩
  · rintro (⟨U, hU, rfl⟩ | ⟨V, hV, rfl⟩)
    · exact Or.inl ⟨U, hU, rfl⟩
    · exact Or.inr ⟨V, hV, rfl⟩

/-- Theorem 15.2: The preimages of open sets under `π₁` and `π₂` form a
subbasis for the product topology on `X × Y`. -/
theorem prod_eq_generateFrom_projections {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] :
    (inferInstance : TopologicalSpace (X × Y)) =
      generateFrom (prodSubbasis X Y) := by
  rw [prodSubbasis, generateFrom_union, ← induced_generateFrom_eq,
    ← induced_generateFrom_eq, generateFrom_setOf_isOpen, generateFrom_setOf_isOpen]
  rfl

end TopologicalSpace
