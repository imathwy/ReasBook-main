module

public import Topology_Munkres_2000.Book.Assumption_9_1.ChoiceSet
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Pairwise.Basic

public section

universe u

namespace Set.Finite

/-- Helper for Definition 9.2: adjoining `x ∈ A` to a set disjoint from `A`
makes its intersection with `A` the singleton `{x}`. -/
lemma insert_inter_eq_singleton_of_mem_of_disjoint {α : Type u} {A C : Set α} {x : α}
    (hx : x ∈ A) (hdisjoint : Disjoint C A) : insert x C ∩ A = {x} := by
  -- Compare membership on both sides and use disjointness to exclude old points of `C`.
  ext y
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyx | hyC, hyA⟩
    · exact hyx
    · exact False.elim ((Set.disjoint_left.mp hdisjoint) hyC hyA)
  · intro hyx
    subst y
    exact ⟨Or.inl rfl, hx⟩

/-- Helper for Definition 9.2: a choice set extends across a new set disjoint
from the union of the old collection by adjoining one point of the new set. -/
lemma isChoiceSet_insert_of_disjoint {α : Type u} {𝒜 : Set (Set α)} {A C : Set α} {x : α}
    (hC : 𝒜.IsChoiceSet C) (hx : x ∈ A) (hdisjoint : Disjoint A (⋃₀ 𝒜)) :
    (insert A 𝒜).IsChoiceSet (insert x C) := by
  apply Set.IsChoiceSet.mk
  · -- Every selected point lies in either the new set or the old union.
    intro y hy
    rw [Set.sUnion_insert]
    rcases hy with hyx | hyC
    · subst y
      exact Set.mem_union_left _ hx
    · exact Set.mem_union_right _ (hC.subset_sUnion hyC)
  · -- The new member has intersection `{x}`, while old intersections are unchanged.
    intro B hB
    rcases hB with hBA | hB
    · subst B
      have hCA : Disjoint C A := by
        refine Set.disjoint_left.mpr ?_
        intro y hyC hyA
        exact (Set.disjoint_left.mp hdisjoint) hyA (hC.subset_sUnion hyC)
      rw [insert_inter_eq_singleton_of_mem_of_disjoint hx hCA]
      simp only [Set.mem_singleton_iff]
      exact ⟨x, rfl, fun y hy ↦ hy⟩
    · have hAB : Disjoint A B := (Set.disjoint_sUnion_right.mp hdisjoint) B hB
      have hxB : x ∉ B := fun hxB ↦ (Set.disjoint_left.mp hAB) hx hxB
      rw [Set.insert_inter_of_notMem hxB]
      exact hC.existsUnique_mem_inter hB

/-- Definition 9.2: Given a finite collection `𝒜` of pairwise disjoint nonempty
sets, there is a set `C` consisting of exactly one element from each member of
`𝒜`. -/
theorem exists_isChoiceSet {α : Type u} {𝒜 : Set (Set α)} (hfinite : 𝒜.Finite)
    (hdisjoint : 𝒜.PairwiseDisjoint id)
    (hnonempty : ∀ A ∈ 𝒜, A.Nonempty) :
    ∃ C, 𝒜.IsChoiceSet C := by
  -- Generalize the structural hypotheses so that the finite induction hypothesis can reuse them.
  revert hdisjoint hnonempty
  refine Set.Finite.induction_on 𝒜 hfinite ?_ ?_
  · intro hdisjoint hnonempty
    refine ⟨∅, Set.IsChoiceSet.mk ?_ ?_⟩
    · intro x hx
      exact False.elim hx
    · intro A hA
      exact False.elim hA
  · intro A 𝒜 hA hfinite ih hdisjoint hnonempty
    -- Separate the new set's conditions from those of the residual collection.
    have hparts := (Set.pairwiseDisjoint_insert_of_notMem hA).mp hdisjoint
    have hnonemptyA : A.Nonempty := hnonempty A (Set.mem_insert A 𝒜)
    have hnonemptyOld : ∀ B ∈ 𝒜, B.Nonempty := by
      intro B hB
      exact hnonempty B (Set.mem_insert_of_mem A hB)
    obtain ⟨C, hC⟩ := ih hparts.1 hnonemptyOld
    obtain ⟨x, hx⟩ := hnonemptyA
    have hAunion : Disjoint A (⋃₀ 𝒜) := Set.disjoint_sUnion_right.mpr hparts.2
    -- Adjoin the selected point using the extension interface proved above.
    exact ⟨insert x C, isChoiceSet_insert_of_disjoint hC hx hAunion⟩

end Set.Finite
