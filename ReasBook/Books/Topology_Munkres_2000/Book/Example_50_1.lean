module

public import Topology_Munkres_2000.Book.Example_50_1.RealSubspace

public section

open scoped CoveringDimension

namespace Set

/-- Example 50.1. Every compact subspace of `ℝ` has topological dimension at most `1`.
The compactness assumption is unnecessary: the result holds for every subspace of `ℝ`. -/
theorem real_coveringDimension_le_one (X : Set ℝ) :
    dim X ≤ 1 := by
  -- Build an interval refinement, discard redundant members, and use the order bound.
  refine (coveringDimension_le_iff X 1).mpr ?_
  intro 𝒜 hopen hcover
  obtain ⟨𝒱, h𝒱refines, h𝒱cover, h𝒱ord, h𝒱finite⟩ :=
    existsPointFiniteOrdConnectedOpenRefinement X 𝒜 hopen hcover
  obtain ⟨𝒲, h𝒲sub, h𝒲cover, h𝒲irr⟩ :=
    existsIrredundantSubcover_of_pointFinite 𝒱 h𝒱cover h𝒱finite
  refine ⟨𝒲, ?_, h𝒲cover, ?_⟩
  · rw [isOpenRefinement_iff]
    constructor
    · exact ⟨fun hW ↦ h𝒱refines.subset_of_mem (h𝒲sub hW)⟩
    · exact fun W hW ↦ h𝒱refines.isOpen_of_mem (h𝒲sub hW)
  · simpa only [Nat.reduceAdd] using
      hasOrderLE_two_of_irredundant_ordConnected_cover 𝒲 h𝒲cover
        (fun W hW ↦ h𝒱ord W (h𝒲sub hW)) h𝒲irr

/-- The open-cover characterization of Example 50.1 for every subspace of `ℝ`. -/
theorem real_hasCoveringDimensionLE_one (X : Set ℝ) :
    HasCoveringDimensionLE X 1 :=
  (coveringDimension_le_iff X 1).mp (real_coveringDimension_le_one X)

end Set
