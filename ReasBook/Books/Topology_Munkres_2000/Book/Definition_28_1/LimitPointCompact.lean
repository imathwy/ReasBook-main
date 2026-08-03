module

public import Topology_Munkres_2000.Book.Definition_28_1

public section

universe u

/-- The defining characterization of a limit point compact space. -/
theorem limitPointCompactSpace_iff (X : Type u) [TopologicalSpace X] :
    LimitPointCompactSpace X ↔
      ∀ s : Set X, s.Infinite → ∃ x, AccPt x (Filter.principal s) := by
  constructor
  · intro h
    -- Project the quantified property from the class witness.
    exact h.exists_accPt
  · intro h
    -- Repackage the quantified property as the single class field.
    exact ⟨h⟩

/-- In a `T₁` space, limit point compactness is equivalent to countable compactness. -/
theorem limitPointCompactSpace_iff_countablyCompactSpace
    (X : Type u) [TopologicalSpace X] [T1Space X] :
    LimitPointCompactSpace X ↔ CountablyCompactSpace X := by
  constructor
  · intro h
    refine ⟨isCountablyCompact_iff_infinite_subset_has_accPt.2 ?_⟩
    intro s _ hs
    obtain ⟨x, hx⟩ := h.exists_accPt s hs
    exact ⟨x, Set.mem_univ x, hx⟩
  · intro h
    refine ⟨fun s hs ↦ ?_⟩
    obtain ⟨x, _, hx⟩ := isCountablyCompact_iff_infinite_subset_has_accPt.1
      h.isCountablyCompact_univ s (Set.subset_univ s) hs
    exact ⟨x, hx⟩

/-- Every countably compact topological space is limit point compact. -/
instance CountablyCompactSpace.toLimitPointCompactSpace (X : Type u) [TopologicalSpace X]
    [CountablyCompactSpace X] : LimitPointCompactSpace X := by
  refine ⟨fun s hs ↦ ?_⟩
  -- Apply countable compactness on the whole space and discard membership in `Set.univ`.
  obtain ⟨x, _, hx⟩ :=
    CountablyCompactSpace.isCountablyCompact_univ.exists_accPt_of_infinite
      (Set.subset_univ s) hs
  exact ⟨x, hx⟩
