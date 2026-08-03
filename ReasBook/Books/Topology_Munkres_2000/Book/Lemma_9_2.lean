module

public import Topology_Munkres_2000.Book.Definition_9_1.ChoiceFunction

public section

open Set

universe u

/-- Lemma 9.2 (Existence of a choice function). A collection of nonempty sets admits
a choice function valued in its union. -/
theorem existsChoiceFunction {α : Type u} (𝓑 : Set (Set α))
    (h𝓑 : ∀ B ∈ 𝓑, B.Nonempty) :
    ∃ c : 𝓑 → ⋃₀ 𝓑, 𝓑.IsChoiceFunction c := by
  classical
  -- Choose one point from each member of the collection.
  have selectedMem (B : 𝓑) :
      Classical.choose (h𝓑 B B.property) ∈ (B : Set α) := by
    exact Classical.choose_spec (h𝓑 B B.property)
  -- Each selected point lies in the union, so it defines an element of the codomain subtype.
  have selectedMemUnion (B : 𝓑) :
      Classical.choose (h𝓑 B B.property) ∈ ⋃₀ 𝓑 := by
    exact mem_sUnion_of_mem (selectedMem B) B.property
  let c : 𝓑 → ⋃₀ 𝓑 := fun B ↦
    ⟨Classical.choose (h𝓑 B B.property), selectedMemUnion B⟩
  -- The defining membership property identifies the constructed map as a choice function.
  have cIsChoice : 𝓑.IsChoiceFunction c := by
    apply Set.IsChoiceFunction.of_mem
    intro B
    exact selectedMem B
  exact ⟨c, cIsChoice⟩
