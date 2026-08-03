module

public import Topology_Munkres_2000.Book.Assumption_9_1.ChoiceSet
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Order.RelClasses
public import Mathlib.SetTheory.Cardinal.Order

public section

universe u

namespace Set

/-- Helper for Exercise 1.99.7: the range of a selector for a pairwise disjoint family is a
choice set. -/
private lemma isChoiceSet_range_of_selector {α : Type u} {𝒜 : Set (Set α)}
    (hdisjoint : 𝒜.PairwiseDisjoint id) (choose : 𝒜 → α)
    (hchoose : ∀ A : 𝒜, choose A ∈ (A : Set α)) :
    𝒜.IsChoiceSet (Set.range choose) := by
  classical
  -- Every selected element lies in the union through its indexing family member.
  refine Set.IsChoiceSet.mk ?_ ?_
  · rintro x ⟨A, rfl⟩
    exact Set.mem_sUnion_of_mem (hchoose A) A.property
  · intro A hA
    let indexedA : 𝒜 := ⟨A, hA⟩
    -- The selector value at `A` supplies the required intersection witness.
    refine ⟨choose indexedA, ⟨⟨indexedA, rfl⟩, hchoose indexedA⟩, ?_⟩
    intro x hx
    obtain ⟨B, hBx⟩ := hx.1
    -- Disjointness forces the member selecting `x` to be the indexed set `A`.
    have hBA : (B : Set α) = A := by
      by_contra hne
      have hsetsDisjoint : Disjoint (B : Set α) A := hdisjoint B.property hA hne
      exact Set.disjoint_left.mp hsetsDisjoint (hchoose B) (hBx ▸ hx.2)
    have hsubtypes : B = indexedA := Subtype.ext hBA
    rw [← hBx, hsubtypes]

end Set

/-- Exercise 1.99.7: The axiom of choice for pairwise disjoint families of
nonempty sets is equivalent to the well-ordering theorem. -/
theorem axiomOfChoiceForDisjointSets_iff_wellOrderingTheorem :
    (∀ {α : Type u} (𝒜 : Set (Set α)),
      𝒜.PairwiseDisjoint id → (∀ A ∈ 𝒜, A.Nonempty) →
        ∃ C, 𝒜.IsChoiceSet C) ↔
    (∀ α : Type u, ∃ r : α → α → Prop, IsWellOrder α r) := by
  constructor
  · intro _ α
    -- Mathlib's canonical relation well-orders every type.
    exact ⟨WellOrderingRel, inferInstance⟩
  · intro wellOrdering α 𝒜 hdisjoint hnonempty
    classical
    -- Well-order the ambient type and select the least point of each family member.
    obtain ⟨r, hwellOrder⟩ := wellOrdering α
    let choose : 𝒜 → α := fun A ↦ hwellOrder.wf.min A (hnonempty A A.property)
    have hchoose : ∀ A : 𝒜, choose A ∈ (A : Set α) := by
      intro A
      exact hwellOrder.wf.min_mem A (hnonempty A A.property)
    -- The selector range meets every pairwise disjoint member exactly once.
    exact ⟨Set.range choose, Set.isChoiceSet_range_of_selector hdisjoint choose hchoose⟩

end
