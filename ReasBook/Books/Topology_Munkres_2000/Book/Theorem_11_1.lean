module

public import Mathlib.Order.Zorn

public section

/-- Theorem 11.1 (The maximum principle): every relation has a maximal chain.
In particular, every strict partial order has a maximal simply ordered subset. -/
theorem existsMaxChain {α : Type u} (r : α → α → Prop) : ∃ B : Set α, IsMaxChain r B := by
  obtain ⟨B, hB, _⟩ := (IsChain.empty : IsChain r (∅ : Set α)).exists_maxChain
  exact ⟨B, hB⟩

end
