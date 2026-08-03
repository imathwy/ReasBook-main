module

public import Topology_Munkres_2000.Book.Definition_11_4
import all Topology_Munkres_2000.Book.Definition_11_4
public import Topology_Munkres_2000.Book.Theorem_11_1

public section

namespace StrictOrder

/-- Helper for Lemma 11.1: an upper bound compares every member with the bound. -/
private lemma upperBound_compare {α : Type u} {r : α → α → Prop}
    {B : Set α} {c : α} (hc : IsUpperBound r B c) :
    ∀ b ∈ B, b = c ∨ r b c := by
  -- Route correction: `import all` exposes the definition privately, so the hypothesis computes
  -- directly to the comparison property needed by the chain argument.
  exact hc

/-- Helper for Lemma 11.1: absence of strict successors gives maximality. -/
private lemma isMaximal_of_no_successor {α : Type u} {r : α → α → Prop} {m : α}
    (h : ∀ a, ¬r m a) : IsMaximal r m := by
  -- The privately exposed definition identifies maximality with having no strict successor.
  exact h

/-- Helper for Lemma 11.1: an upper bound of a maximal chain belongs to that chain. -/
private lemma upperBound_mem_of_isMaxChain {α : Type u} {r : α → α → Prop}
    {B : Set α} {c : α} (hB : IsMaxChain r B) (hc : IsUpperBound r B c) : c ∈ B := by
  -- Adjoining the upper bound preserves comparability with every chain element.
  have hBc : IsChain r (Set.insert c B) := hB.isChain.insert fun b hb hcb ↦ by
    rcases upperBound_compare hc b hb with hbc | hbc
    · exact (hcb hbc.symm).elim
    · exact Or.inr hbc
  -- Maximality identifies the enlarged chain with the original one.
  have hEq : B = Set.insert c B := hB.2 hBc (Set.subset_insert c B)
  rw [hEq]
  exact Set.mem_insert c B

/-- Helper for Lemma 11.1: a point above an upper bound can be adjoined to the chain. -/
private lemma isChain_insert_of_upperBound_rel {α : Type u} {r : α → α → Prop}
    [IsTrans α r] {B : Set α} {c d : α} (hB : IsChain r B)
    (hc : IsUpperBound r B c) (hcd : r c d) : IsChain r (Set.insert d B) := by
  -- Every old chain element lies below `d`, either directly or through `c`.
  refine hB.insert fun b hb _ ↦ ?_
  rcases upperBound_compare hc b hb with hbc | hbc
  · exact Or.inr (hbc ▸ hcd)
  · exact Or.inr (IsTrans.trans b c d hbc hcd)

/-- Helper for Lemma 11.1: an upper bound of a maximal chain is a maximal element. -/
private lemma isMaximal_of_isMaxChain_upperBound {α : Type u} {r : α → α → Prop}
    [IsStrictOrder α r] {B : Set α} {c : α} (hB : IsMaxChain r B)
    (hc : IsUpperBound r B c) : IsMaximal r c := by
  -- It suffices to rule out every strict successor of the chosen bound.
  refine isMaximal_of_no_successor fun d hcd ↦ ?_
  -- A hypothetical strict successor also extends the chain, hence lies in it.
  have hBd : IsChain r (Set.insert d B) :=
    isChain_insert_of_upperBound_rel hB.isChain hc hcd
  have hEq : B = Set.insert d B := hB.2 hBd (Set.subset_insert d B)
  have hd : d ∈ B := by
    rw [hEq]
    exact Set.mem_insert d B
  -- The upper-bound alternatives both contradict `c < d`.
  rcases upperBound_compare hc d hd with hdc | hdc
  · exact (irrefl c) (hdc ▸ hcd)
  · exact (asymm hcd hdc)

/-- Lemma 11.1 (Zorn's lemma): if every simply ordered subset of a strict partial
order has an upper bound, then the order has a maximal element. -/
theorem exists_maximal_of_chains_bounded {α : Type u} (r : α → α → Prop)
    [IsStrictOrder α r]
    (h : ∀ B : Set α, IsChain r B → ∃ c, IsUpperBound r B c) :
    ∃ m, IsMaximal r m := by
  -- The maximum principle supplies a maximal simply ordered subset.
  obtain ⟨B, hB⟩ := existsMaxChain r
  -- Its given upper bound is maximal by the insertion argument above.
  obtain ⟨c, hc⟩ := h B hB.isChain
  exact ⟨c, isMaximal_of_isMaxChain_upperBound hB hc⟩

end StrictOrder

end
