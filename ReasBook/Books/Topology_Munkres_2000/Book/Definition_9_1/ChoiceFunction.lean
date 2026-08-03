module

public import Mathlib.Data.Set.Lattice

public section

universe u

namespace Set

/-- A function is a choice function for a collection of sets when it selects an element
of each set in the collection. -/
def IsChoiceFunction {α : Type u} (𝓑 : Set (Set α)) (c : 𝓑 → ⋃₀ 𝓑) : Prop :=
  ∀ B : 𝓑, (c B : α) ∈ (B : Set α)

/-- A function selecting an element of every set in the collection is a choice function. -/
theorem IsChoiceFunction.of_mem {α : Type u} {𝓑 : Set (Set α)} {c : 𝓑 → ⋃₀ 𝓑}
    (h : ∀ B : 𝓑, (c B : α) ∈ (B : Set α)) : 𝓑.IsChoiceFunction c := by
  exact h

/-- A choice function selects an element of each set in its collection. -/
theorem IsChoiceFunction.mem {α : Type u} {𝓑 : Set (Set α)} {c : 𝓑 → ⋃₀ 𝓑}
    (hc : 𝓑.IsChoiceFunction c) (B : 𝓑) : (c B : α) ∈ (B : Set α) := by
  exact hc B

end Set
