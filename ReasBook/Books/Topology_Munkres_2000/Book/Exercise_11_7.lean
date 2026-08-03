module

public import Mathlib.Order.TeichmullerTukey

import Topology_Munkres_2000.Book.Exercise_11_6

public section

/-- The family of chains for any relation is of finite character. -/
theorem isOfFiniteCharacter_isChain {α : Type u} (r : α → α → Prop) :
    Order.IsOfFiniteCharacter {s : Set α | IsChain r s} := by
  intro s
  constructor
  · intro hs t hts _
    exact hs.mono hts
  · intro hs x hx y hy hxy
    have hpair := hs ({x, y} : Set α) (Set.pair_subset_iff.mpr ⟨hx, hy⟩) (by simp)
    exact hpair (by simp) (by simp) hxy

/-- Exercise 11.7: Tukey's lemma implies the Hausdorff maximum principle: every relation has a
maximal chain. In particular, this applies to every strict partial order. -/
theorem existsMaxChain_of_tukey {α : Type u} (r : α → α → Prop) :
    ∃ s : Set α, IsMaxChain r s := by
  obtain ⟨s, hs⟩ :=
    existsMaximalOfFiniteType (isOfFiniteCharacter_isChain r) ⟨∅, IsChain.empty⟩
  exact ⟨s, hs.1, fun _ ht hst ↦ Set.Subset.antisymm hst (hs.2 ht hst)⟩
