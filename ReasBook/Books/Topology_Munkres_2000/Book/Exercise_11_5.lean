module

public import Mathlib.Order.Zorn

public section

/-- Exercise 11.5: Kuratowski's lemma states that a collection of sets closed under
unions of subcollections simply ordered by proper inclusion has a maximal member. -/
theorem existsMaximalOfChainSUnionMem {X : Type u} {𝒜 : Set (Set X)}
    (h𝒜 : ∀ 𝓑 : Set (Set X), 𝓑 ⊆ 𝒜 → IsChain (· ⊂ ·) 𝓑 → ⋃₀ 𝓑 ∈ 𝒜) :
    ∃ B, Maximal (· ∈ 𝒜) B := by
  apply zorn_subset 𝒜
  intro 𝓑 h𝓑 hchain
  refine ⟨⋃₀ 𝓑, h𝒜 𝓑 h𝓑 ?_, fun _ h ↦ Set.subset_sUnion_of_mem h⟩
  intro A hA B hB hAB
  exact (hchain hA hB hAB).imp
    (fun h ↦ Set.ssubset_iff_subset_ne.mpr ⟨h, hAB⟩)
    (fun h ↦ Set.ssubset_iff_subset_ne.mpr ⟨h, hAB.symm⟩)

end
