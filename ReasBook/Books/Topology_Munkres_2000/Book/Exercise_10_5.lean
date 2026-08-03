module

public import Topology_Munkres_2000.Book.Assumption_9_1.ChoiceSet
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Order.RelClasses

public section

universe u

namespace Set

/-- Helper for Exercise 10.5: the range of a selector for a pairwise disjoint family is a choice
set. -/
lemma isChoiceSet_range_of_mem {α : Type u} {𝒜 : Set (Set α)}
    (hdisjoint : 𝒜.PairwiseDisjoint id) (choose : 𝒜 → α)
    (hchoose : ∀ A : 𝒜, choose A ∈ (A : Set α)) :
    𝒜.IsChoiceSet (Set.range choose) := by
  classical
  -- Every selected element belongs to the union through its indexing family member.
  refine Set.IsChoiceSet.mk ?_ ?_
  · rintro x ⟨A, rfl⟩
    exact Set.mem_sUnion_of_mem (hchoose A) A.property
  · intro A hA
    let indexedA : 𝒜 := ⟨A, hA⟩
    -- The element selected from `A` supplies the required intersection witness.
    refine ⟨choose indexedA, ⟨⟨indexedA, rfl⟩, hchoose indexedA⟩, ?_⟩
    intro x hx
    obtain ⟨B, hBx⟩ := hx.1
    -- Pairwise disjointness forces any family member selecting `x` to equal `A`.
    have hBA : (B : Set α) = A := by
      by_contra hne
      have hsetsDisjoint : Disjoint (B : Set α) A := hdisjoint B.property hA hne
      exact Set.disjoint_left.mp hsetsDisjoint (hchoose B) (hBx ▸ hx.2)
    have hsubtypes : B = indexedA := Subtype.ext hBA
    rw [← hBx, hsubtypes]

end Set

/-- Exercise 10.5: The well-ordering theorem implies the choice axiom. -/
theorem wellOrderingImpliesAxiomOfChoice
    (wellOrdering : ∀ α : Type u, ∃ r : α → α → Prop, IsWellOrder α r)
    {α : Type u} (𝒜 : Set (Set α)) (hdisjoint : 𝒜.PairwiseDisjoint id)
    (hnonempty : ∀ A ∈ 𝒜, A.Nonempty) :
    ∃ C, 𝒜.IsChoiceSet C := by
  classical
  -- Well-order the ambient type so each nonempty family member has a least element.
  obtain ⟨r, hwellOrder⟩ := wellOrdering α
  let choose : 𝒜 → α := fun A ↦ hwellOrder.wf.min A (hnonempty A A.property)
  have hchoose : ∀ A : 𝒜, choose A ∈ (A : Set α) := by
    intro A
    exact hwellOrder.wf.min_mem A (hnonempty A A.property)
  -- The range of these least-element choices meets each disjoint member exactly once.
  exact ⟨Set.range choose, Set.isChoiceSet_range_of_mem hdisjoint choose hchoose⟩
