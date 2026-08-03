module

public import Topology_Munkres_2000.Book.Definition_28_1.LimitPointCompact

public section

universe u

/-- Exercise 28.4: For a T₁ space, countable compactness is equivalent to limit point
compactness. -/
theorem countablyCompactSpace_iff_limitPointCompactSpace (X : Type u) [TopologicalSpace X]
    [T1Space X] : CountablyCompactSpace X ↔ LimitPointCompactSpace X := by
  constructor
  · intro h
    refine ⟨fun s hs ↦ ?_⟩
    obtain ⟨x, -, hx⟩ :=
      h.isCountablyCompact_univ.exists_accPt_of_infinite (Set.subset_univ s) hs
    exact ⟨x, hx⟩
  · intro h
    rw [← isCountablyCompact_univ_iff, isCountablyCompact_iff_infinite_subset_has_accPt]
    intro s _ hs
    obtain ⟨x, hx⟩ := h.exists_accPt s hs
    exact ⟨x, Set.mem_univ x, hx⟩
