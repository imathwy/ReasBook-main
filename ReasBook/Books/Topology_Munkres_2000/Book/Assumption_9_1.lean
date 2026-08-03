module

public import Topology_Munkres_2000.Book.Assumption_9_1.ChoiceSet
public import Mathlib.Data.Set.Pairwise.Basic

public section

open Set

universe u

/-- Helper for Assumption 9.1: the range of a subtype-valued selection lies in the
union of its indexing family. -/
private lemma range_subtypeSelection_subset_sUnion {α : Type u} {𝒜 : Set (Set α)}
    (choose : (A : 𝒜) → ↥(A : Set α)) :
    Set.range (fun A : 𝒜 ↦ (choose A : α)) ⊆ ⋃₀ 𝒜 := by
  -- A selected point lies in the union through the family member that indexes it.
  rintro x ⟨A, rfl⟩
  exact Set.mem_sUnion_of_mem (choose A).property A.property

/-- Helper for Assumption 9.1: a subtype-valued selection from a pairwise disjoint
family meets each indexed set in exactly its selected point. -/
private lemma existsUnique_mem_inter_range_subtypeSelection {α : Type u}
    {𝒜 : Set (Set α)} (hdisjoint : 𝒜.PairwiseDisjoint id)
    (choose : (A : 𝒜) → ↥(A : Set α)) {A : Set α} (hA : A ∈ 𝒜) :
    ∃! x, x ∈ Set.range (fun B : 𝒜 ↦ (choose B : α)) ∩ A := by
  let indexedA : 𝒜 := ⟨A, hA⟩
  -- The point selected from `A` supplies the intersection witness.
  refine ⟨choose indexedA, ⟨⟨indexedA, rfl⟩, (choose indexedA).property⟩, ?_⟩
  rintro x ⟨⟨B, rfl⟩, hxA⟩
  -- Disjointness forces the set indexing any other intersection point to be `A`.
  have hBA : (B : Set α) = A := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisjoint B.property hA hne) (choose B).property hxA
  have hB : B = indexedA := Subtype.ext hBA
  subst B
  rfl

/-- Assumption 9.1 (Axiom of choice): Given a collection `𝒜` of pairwise disjoint
nonempty sets, there is a set `C` consisting of exactly one element from each
member of `𝒜`. -/
theorem axiomOfChoiceForDisjointSets {α : Type u} (𝒜 : Set (Set α))
    (hdisjoint : 𝒜.PairwiseDisjoint id) (hnonempty : ∀ A ∈ 𝒜, A.Nonempty) :
    ∃ C, 𝒜.IsChoiceSet C := by
  classical
  let choose : (A : 𝒜) → ↥(A : Set α) := fun A ↦
    Classical.choice (hnonempty A A.property).to_subtype
  -- The range of the selected points satisfies both defining choice-set clauses.
  refine ⟨Set.range (fun A : 𝒜 ↦ (choose A : α)), Set.IsChoiceSet.mk ?_ ?_⟩
  · exact range_subtypeSelection_subset_sUnion choose
  · intro A hA
    exact existsUnique_mem_inter_range_subtypeSelection hdisjoint choose hA
