module

public import Mathlib.Topology.Bases

public section

open Set
open TopologicalSpace

universe u

/-- Exercise 30.13: If a topological space has a countable dense subset, then every
pairwise disjoint collection of open subsets is countable. -/
theorem Set.PairwiseDisjoint.countable_of_isOpen_id
    {X : Type u} [TopologicalSpace X] [SeparableSpace X] {𝒰 : Set (Set X)}
    (hdisjoint : 𝒰.PairwiseDisjoint id) (hopen : ∀ U ∈ 𝒰, IsOpen U) :
    𝒰.Countable := by
  have hcountable : (𝒰 \ {∅}).Countable :=
    (hdisjoint.subset sdiff_subset).countable_of_isOpen
      (fun U hU ↦ hopen U hU.1) (fun U hU ↦ nonempty_iff_ne_empty.2 hU.2)
  refine (hcountable.union (countable_singleton ∅)).mono ?_
  intro U hU
  by_cases hUempty : U = ∅
  · exact Or.inr (by simp [hUempty])
  · exact Or.inl ⟨hU, by simp [hUempty]⟩
