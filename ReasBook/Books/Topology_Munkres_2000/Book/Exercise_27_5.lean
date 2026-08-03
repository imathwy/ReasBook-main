module

public import Mathlib.Topology.Baire.LocallyCompactRegular

public section

open Set

universe u v

namespace IsMeagre

/-- A meagre subset of a Baire space has empty interior. -/
theorem interior_eq_empty {X : Type u} [TopologicalSpace X] [BaireSpace X]
    {s : Set X} (hs : IsMeagre s) : interior s = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  intro x hx
  exact not_isMeagre_of_isOpen isOpen_interior ⟨x, hx⟩ (hs.mono interior_subset)

end IsMeagre

/-- Exercise 27.5: In a compact Hausdorff space, a countable union of closed sets
with empty interior has empty interior. -/
theorem interior_iUnion_eq_empty_of_closed
    {X : Type u} {ι : Type v} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Countable ι] (A : ι → Set X) (h_closed : ∀ i, IsClosed (A i))
    (h_interior : ∀ i, interior (A i) = ∅) :
    interior (⋃ i, A i) = ∅ := by
  apply IsMeagre.interior_eq_empty
  exact isMeagre_iUnion fun i ↦
    ((h_closed i).isNowhereDense_iff.2 (h_interior i)).isMeagre
