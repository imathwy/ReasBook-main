module

public import Mathlib.Data.Set.Prod

@[expose] public section

universe u v

namespace Set

/-- Inclusion between nonempty Cartesian products is equivalent to coordinatewise inclusion. -/
theorem univ_pi_subset_iff {ι : Type u} {α : ι → Type v} {A B : ∀ i, Set (α i)}
    (hB : (univ.pi B).Nonempty) :
    univ.pi B ⊆ univ.pi A ↔ ∀ i, B i ⊆ A i := by
  classical
  constructor
  · intro h i x hx
    obtain ⟨b, hb⟩ := hB
    have h_update : Function.update b i x ∈ univ.pi B := by
      intro j _
      by_cases hji : j = i
      · subst j
        simpa using hx
      · simpa [Function.update_of_ne hji] using hb j (mem_univ j)
    simpa using h h_update i (mem_univ i)
  · exact fun h ↦ pi_mono fun i _ ↦ h i

/-- The union of two Cartesian products lies in the product of coordinatewise unions. -/
theorem union_univ_pi_subset {ι : Type u} {α : ι → Type v} (A B : ∀ i, Set (α i)) :
    univ.pi A ∪ univ.pi B ⊆ univ.pi (fun i ↦ A i ∪ B i) := by
  intro x hx i _
  exact hx.elim (fun h ↦ Or.inl (h i (mem_univ i)))
    (fun h ↦ Or.inr (h i (mem_univ i)))

end Set
