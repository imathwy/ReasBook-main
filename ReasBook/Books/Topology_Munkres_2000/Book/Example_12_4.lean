module

public import Mathlib.Topology.Constructions
public import Mathlib.Order.Filter.Cocardinal

public section

open Set

universe u

namespace TopologicalSpace

/-- Helper for Example 12.4: the universal set has countable complement. -/
lemma cocountableIsOpenUniv (X : Type u) :
    (Set.univ : Set X) = ∅ ∨ (Set.univ : Set X)ᶜ.Countable := by
  -- The complement of the universal set is empty, hence countable.
  right
  simp only [compl_univ, countable_empty]

/-- Helper for Example 12.4: empty-or-countable-complement sets are closed under intersections. -/
lemma cocountableIsOpenInter {X : Type u} (s t : Set X)
    (hs : s = ∅ ∨ sᶜ.Countable) (ht : t = ∅ ∨ tᶜ.Countable) :
    s ∩ t = ∅ ∨ (s ∩ t)ᶜ.Countable := by
  -- If either set is empty, so is the intersection; otherwise unite the countable complements.
  rcases hs with rfl | hs
  · left
    exact empty_inter t
  rcases ht with rfl | ht
  · left
    exact inter_empty s
  · right
    rw [compl_inter]
    exact hs.union ht

/-- Helper for Example 12.4: empty-or-countable-complement sets are closed under arbitrary
unions. -/
lemma cocountableIsOpenSUnion {X : Type u} (S : Set (Set X))
    (hS : ∀ s ∈ S, s = ∅ ∨ sᶜ.Countable) :
    ⋃₀ S = ∅ ∨ (⋃₀ S)ᶜ.Countable := by
  -- A nonempty union contains a member whose complement controls the union's complement.
  rw [or_iff_not_imp_left]
  intro hne
  rcases Set.nonempty_iff_ne_empty.mpr hne with ⟨x, hx⟩
  rcases Set.mem_sUnion.mp hx with ⟨s, hsS, hxs⟩
  rcases hS s hsS with hs | hs
  · subst s
    simp only [Set.mem_empty_iff_false] at hxs
  · exact hs.mono (compl_subset_compl.mpr (Set.subset_sUnion_of_mem hsS))

/-- Example 12.4: The topology whose open sets are empty or have countable complement. -/
@[implicit_reducible]
protected def cocountable (X : Type u) : TopologicalSpace X where
  IsOpen s := s = ∅ ∨ sᶜ.Countable
  isOpen_univ := cocountableIsOpenUniv X
  isOpen_inter := cocountableIsOpenInter
  isOpen_sUnion := cocountableIsOpenSUnion

/-- Helper for Example 12.4: openness in `TopologicalSpace.cocountable X` is its defining
empty-or-countable-complement condition. -/
lemma cocountable_isOpen {X : Type u} {s : Set X} :
    (TopologicalSpace.cocountable X).IsOpen s ↔ s = ∅ ∨ sᶜ.Countable := by
  rfl

end TopologicalSpace
