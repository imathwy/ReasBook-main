module

public import Topology_Munkres_2000.Book.Lemma_23_1
public import Topology_Munkres_2000.Book.Example_23_2.PuncturedInterval

public section

open Set

namespace PuncturedInterval

/-- Helper for Example 23.2: the negative and positive halves are separated in `ℝ`. -/
lemma halves_areSeparated : AreSeparated left right := by
  -- Normalize both closures and exclude an intersection at the missing endpoint.
  have hneg : (-1 : ℝ) ≠ 0 := by
    norm_num
  have hpos : (0 : ℝ) ≠ 1 := by
    norm_num
  apply areSeparated_of_disjoint_closure
  · rw [closure_Ico hneg, disjoint_left]
    intro x hxLeft hxRight
    exact (not_lt_of_ge hxLeft.2) hxRight.1
  · rw [closure_Ioc hpos, disjoint_left]
    intro x hxLeft hxRight
    exact (not_lt_of_ge hxRight.1) hxLeft.2

/-- Example 23.2 (1): The negative and positive halves form a separation of the
punctured interval `Space`. -/
theorem halves_isSeparation : leftInSpace.IsSeparation rightInSpace := by
  -- Supply the endpoint witnesses and transport ambient separatedness to the subspace.
  have hleft : left.Nonempty := by
    refine ⟨-1, ?_⟩
    constructor
    · exact le_rfl
    · norm_num
  have hright : right.Nonempty := by
    refine ⟨1, ?_⟩
    constructor
    · norm_num
    · exact le_rfl
  have hunion : left ∪ right = Space := rfl
  exact (isSeparation_preimage_val_iff_areSeparated hleft hright hunion).mpr
    halves_areSeparated

/-- Example 23.2 (2): Neither half of the punctured interval is open in the
ambient real line. -/
theorem halves_not_isOpen : ¬ IsOpen left ∧ ¬ IsOpen right := by
  -- Openness would put each included endpoint into the corresponding open interval.
  constructor
  · intro hopen
    have hleftEndpoint : (-1 : ℝ) ∈ Ioo (-1) 0 := by
      rw [← interior_Ico, hopen.interior_eq]
      constructor
      · exact le_rfl
      · norm_num
    exact (lt_irrefl (-1 : ℝ)) hleftEndpoint.1
  · intro hopen
    have hrightEndpoint : (1 : ℝ) ∈ Ioo 0 1 := by
      rw [← interior_Ioc, hopen.interior_eq]
      constructor
      · norm_num
      · exact le_rfl
    exact (lt_irrefl (1 : ℝ)) hrightEndpoint.2

/-- Example 23.2 (3): Neither half of the punctured interval contains an
ambient limit point of the other half. -/
theorem halves_avoid_derivedSet :
    Disjoint left (derivedSet right) ∧ Disjoint right (derivedSet left) := by
  -- Project the two limit-point exclusions from ambient separatedness.
  exact (areSeparated_iff_disjoint_derivedSet.mp halves_areSeparated).2

/-- Example 23.2 (4): The point `0` is an ambient limit point of both halves of
the punctured interval. -/
theorem zero_mem_halves_derivedSet :
    0 ∈ derivedSet left ∧ 0 ∈ derivedSet right := by
  -- Put zero in both closures using the closed-interval formulas.
  have hneg : (-1 : ℝ) ≠ 0 := by
    norm_num
  have hpos : (0 : ℝ) ≠ 1 := by
    norm_num
  have hnegLe : (-1 : ℝ) ≤ 0 := by
    norm_num
  have hzeroLeOne : (0 : ℝ) ≤ 1 := by
    norm_num
  have hzeroClosureLeft : (0 : ℝ) ∈ closure left := by
    rw [closure_Ico hneg]
    exact ⟨hnegLe, le_rfl⟩
  have hzeroClosureRight : (0 : ℝ) ∈ closure right := by
    rw [closure_Ioc hpos]
    exact ⟨le_rfl, hzeroLeOne⟩
  -- Zero belongs to neither half, so the closure decomposition places it in each derived set.
  have hzeroNotLeft : (0 : ℝ) ∉ left := by
    intro hzeroLeft
    exact (lt_irrefl (0 : ℝ)) hzeroLeft.2
  have hzeroNotRight : (0 : ℝ) ∉ right := by
    intro hzeroRight
    exact (lt_irrefl (0 : ℝ)) hzeroRight.1
  rw [closure_eq_self_union_derivedSet left] at hzeroClosureLeft
  rw [closure_eq_self_union_derivedSet right] at hzeroClosureRight
  exact ⟨hzeroClosureLeft.resolve_left hzeroNotLeft,
    hzeroClosureRight.resolve_left hzeroNotRight⟩

end PuncturedInterval
