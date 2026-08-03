module

public import Mathlib.Order.TeichmullerTukey

public section

/-- Exercise 11.6: Tukey's lemma states that every nonempty collection of subsets
of finite type (`Order.IsOfFiniteCharacter`) has a maximal member under inclusion. -/
theorem existsMaximalOfFiniteType {X : Type u} {𝒜 : Set (Set X)}
    (h𝒜 : Order.IsOfFiniteCharacter 𝒜) (hne : 𝒜.Nonempty) :
    ∃ B, Maximal (· ∈ 𝒜) B := by
  obtain ⟨A, hA⟩ := hne
  obtain ⟨B, _, hB⟩ := h𝒜.exists_maximal hA
  exact ⟨B, hB⟩
