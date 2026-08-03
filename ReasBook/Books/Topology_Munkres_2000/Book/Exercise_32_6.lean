module

public import Topology_Munkres_2000.Book.Lemma_23_1.SeparatedSets
public import Mathlib.Topology.Separation.Regular

public section

universe u

/-- A space is completely normal if and only if every pair of separated sets has
 disjoint open neighborhoods. -/
theorem completelyNormalSpace_iff_separatedNhds {X : Type u} [TopologicalSpace X] :
    CompletelyNormalSpace X ↔ ∀ ⦃A B : Set X⦄, A.AreSeparated B → SeparatedNhds A B := by
  constructor
  · rintro ⟨h⟩ A B hAB
    exact separatedNhds_iff_disjoint.2
      (h hAB.disjoint_closure_left hAB.disjoint_closure_right)
  · intro h
    exact ⟨fun A B hA hB ↦
      separatedNhds_iff_disjoint.1 (h (Set.areSeparated_of_disjoint_closure hA hB))⟩

/-- Exercise 32.6: Under the book's `T₁` convention, a space is completely normal if and only if
 every pair of separated sets has disjoint open neighborhoods. -/
theorem t5Space_iff_separatedNhds {X : Type u} [TopologicalSpace X] [T1Space X] :
    T5Space X ↔ ∀ ⦃A B : Set X⦄, A.AreSeparated B → SeparatedNhds A B := by
  rw [← completelyNormalSpace_iff_separatedNhds]
  exact ⟨fun h ↦ h.toCompletelyNormalSpace,
    fun h ↦ { toT1Space := inferInstance, toCompletelyNormalSpace := h }⟩
