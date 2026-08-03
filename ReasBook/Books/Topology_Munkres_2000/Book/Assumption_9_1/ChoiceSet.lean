module

public import Mathlib.Data.Set.Lattice

public section

universe u

namespace Set

/-- A set `C` is a choice set for a collection `𝒜` when it lies in the union of
`𝒜` and meets each member of `𝒜` in exactly one element. -/
def IsChoiceSet {α : Type u} (𝒜 : Set (Set α)) (C : Set α) : Prop :=
  C ⊆ ⋃₀ 𝒜 ∧ ∀ A ∈ 𝒜, ∃! x, x ∈ C ∩ A

/-- Construct a choice set from its two defining properties. -/
theorem IsChoiceSet.mk {α : Type u} {𝒜 : Set (Set α)} {C : Set α}
    (hsubset : C ⊆ ⋃₀ 𝒜) (hunique : ∀ A ∈ 𝒜, ∃! x, x ∈ C ∩ A) :
    𝒜.IsChoiceSet C :=
  ⟨hsubset, hunique⟩

/-- A choice set is contained in the union of its collection. -/
theorem IsChoiceSet.subset_sUnion {α : Type u} {𝒜 : Set (Set α)} {C : Set α}
    (hC : 𝒜.IsChoiceSet C) : C ⊆ ⋃₀ 𝒜 :=
  hC.1

/-- A choice set meets each member of its collection in exactly one element. -/
theorem IsChoiceSet.existsUnique_mem_inter {α : Type u} {𝒜 : Set (Set α)} {C A : Set α}
    (hC : 𝒜.IsChoiceSet C) (hA : A ∈ 𝒜) : ∃! x, x ∈ C ∩ A :=
  hC.2 A hA

end Set
