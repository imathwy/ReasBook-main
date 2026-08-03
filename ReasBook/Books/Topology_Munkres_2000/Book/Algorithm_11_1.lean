module

public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.Comparable

public section

/-- Algorithm 11.1: a chain is maximal if every element outside it is incomparable
with some element of the chain. -/
theorem IsChain.isMaxChain_of_incomparable {α : Type u} {r : α → α → Prop} {s : Set α}
    (hs : IsChain r s)
    (h_incomparable : ∀ x ∉ s, ∃ y ∈ s, IncompRel r x y) :
    IsMaxChain r s := by
  refine ⟨hs, fun t ht hst ↦ Set.Subset.antisymm hst ?_⟩
  intro x hx
  by_contra hxs
  obtain ⟨y, hy, hxy, hyx⟩ := h_incomparable x hxs
  exact (ht hx (hst hy) fun h ↦ hxs (h ▸ hy)).elim hxy hyx

/-- An element outside a maximal chain is incomparable with some element of the chain. -/
theorem IsMaxChain.exists_incomparable {α : Type u} {r : α → α → Prop} {s : Set α}
    (hs : IsMaxChain r s) {x : α} (hx : x ∉ s) :
    ∃ y ∈ s, IncompRel r x y := by
  classical
  by_contra h
  push Not at h
  have h_insert : IsChain r (insert x s) := hs.isChain.insert fun y hy _ ↦
    not_incompRel_iff_symmGen.mp (h y hy)
  have hxs : x ∈ s := by
    rw [hs.2 h_insert (Set.subset_insert x s)]
    exact Set.mem_insert x s
  exact hx hxs

/-- A chain is maximal exactly when every element outside it is incomparable with an element
of the chain. -/
theorem IsChain.isMaxChain_iff_forall_exists_incomparable {α : Type u}
    {r : α → α → Prop} {s : Set α} (hs : IsChain r s) :
    IsMaxChain r s ↔ ∀ x ∉ s, ∃ y ∈ s, IncompRel r x y :=
  ⟨fun h _ hx ↦ h.exists_incomparable hx, hs.isMaxChain_of_incomparable⟩

end
