module

public import Topology_Munkres_2000.Book.Definition_39_4.Refinement
public import Topology_Munkres_2000.Book.Example_39_1.IntegerIntervals

public section

/-- The collection of open intervals `(x, x + 1)` indexed by real numbers. -/
def realUnitIntervals : Set (Set ℝ) :=
  Set.range (fun x : ℝ ↦ Set.Ioo x (x + 1))

/-- A set belongs to `realUnitIntervals` exactly when it is an interval
`(x, x + 1)` for some real number `x`. -/
theorem mem_realUnitIntervals {U : Set ℝ} :
    U ∈ realUnitIntervals ↔ ∃ x : ℝ, Set.Ioo x (x + 1) = U :=
  Iff.rfl

/-- The collection of open intervals `(n, n + 3 / 2)` indexed by integers. -/
def integerThreeHalvesIntervals : Set (Set ℝ) :=
  Set.range (fun n : ℤ ↦ Set.Ioo (n : ℝ) ((n : ℝ) + 3 / 2))

/-- A set belongs to `integerThreeHalvesIntervals` exactly when it is an
interval `(n, n + 3 / 2)` for some integer `n`. -/
theorem mem_integerThreeHalvesIntervals {U : Set ℝ} :
    U ∈ integerThreeHalvesIntervals ↔
      ∃ n : ℤ, Set.Ioo (n : ℝ) ((n : ℝ) + 3 / 2) = U :=
  Iff.rfl

/-- The collection of open intervals `(x, x + 3 / 2)` indexed by real numbers. -/
def realThreeHalvesIntervals : Set (Set ℝ) :=
  Set.range (fun x : ℝ ↦ Set.Ioo x (x + 3 / 2))

/-- A set belongs to `realThreeHalvesIntervals` exactly when it is an interval
`(x, x + 3 / 2)` for some real number `x`. -/
theorem mem_realThreeHalvesIntervals {U : Set ℝ} :
    U ∈ realThreeHalvesIntervals ↔
      ∃ x : ℝ, Set.Ioo x (x + 3 / 2) = U :=
  Iff.rfl

/-- Helper for Exercise 39.4: every real unit interval lies in the
integer-shifted interval indexed by the floor of its left endpoint. -/
private lemma realUnitInterval_subset_integerShiftedInterval_floor (x : ℝ) :
    Set.Ioo x (x + 1) ⊆ integerShiftedInterval ⌊x⌋ := by
  -- The floor bounds control the two endpoints of the containing interval.
  intro y hy
  simp only [Set.mem_Ioo] at hy
  rw [mem_integerShiftedInterval]
  constructor
  · exact lt_of_le_of_lt (Int.floor_le x) hy.1
  · have hxUpper := Int.lt_floor_add_one x
    linarith

/-- Helper for Exercise 39.4: an integer-indexed interval of length `3 / 2`
lies in the integer-shifted interval of length two with the same left endpoint. -/
private lemma integerThreeHalvesInterval_subset_integerShiftedInterval (n : ℤ) :
    Set.Ioo (n : ℝ) ((n : ℝ) + 3 / 2) ⊆ integerShiftedInterval n := by
  -- The left endpoints agree, and `3 / 2 ≤ 2` controls the right endpoints.
  intro x hx
  simp only [Set.mem_Ioo] at hx
  rw [mem_integerShiftedInterval]
  constructor
  · exact hx.1
  · linarith [hx.2]

/-- Helper for Exercise 39.4: the interval based at `3 / 4` of length `3 / 2`
is not contained in any integer-shifted interval of length two. -/
private lemma realThreeHalvesInterval_threeFourths_not_subset_integerShiftedInterval
    (n : ℤ) :
    ¬ Set.Ioo (3 / 4 : ℝ) (3 / 4 + 3 / 2) ⊆ integerShiftedInterval n := by
  intro hSubset
  -- The source interval contains both adjacent integers `1` and `2`.
  have hOne : (1 : ℝ) ∈ Set.Ioo (3 / 4 : ℝ) (3 / 4 + 3 / 2) := by
    norm_num [Set.mem_Ioo]
  have hTwo : (2 : ℝ) ∈ Set.Ioo (3 / 4 : ℝ) (3 / 4 + 3 / 2) := by
    norm_num [Set.mem_Ioo]
  have hOneTarget := hSubset hOne
  have hTwoTarget := hSubset hTwo
  simp only [mem_integerShiftedInterval] at hOneTarget hTwoTarget
  -- Their target memberships would force the integer `n` strictly between `0` and `1`.
  have hnPositiveReal : (0 : ℝ) < (n : ℝ) := by
    linarith [hTwoTarget.2]
  have hnPositive : (0 : ℤ) < n := by
    exact_mod_cast hnPositiveReal
  have hnLessOne : n < (1 : ℤ) := by
    exact_mod_cast hOneTarget.1
  omega

/-- The first conclusion of Exercise 39.4: the collection of real-indexed unit
intervals refines the collection of integer-indexed intervals of length two. -/
instance isRefinement_realUnitIntervals_integerLengthTwoIntervals :
    IsRefinement realUnitIntervals integerLengthTwoIntervals := by
  -- Choose the integer interval indexed by the floor of each source endpoint.
  rw [isRefinement_iff]
  intro U hU
  obtain ⟨x, rfl⟩ := mem_realUnitIntervals.mp hU
  refine ⟨integerShiftedInterval ⌊x⌋, ?_,
    realUnitInterval_subset_integerShiftedInterval_floor x⟩
  exact mem_integerLengthTwoIntervals.mpr ⟨⌊x⌋, rfl⟩

/-- The second conclusion of Exercise 39.4: the collection of integer-indexed
intervals of length `3 / 2` refines the collection of integer-indexed intervals
of length two. -/
instance isRefinement_integerThreeHalvesIntervals_integerLengthTwoIntervals :
    IsRefinement integerThreeHalvesIntervals integerLengthTwoIntervals := by
  -- Keep the same integer left endpoint and enlarge only the right endpoint.
  rw [isRefinement_iff]
  intro U hU
  obtain ⟨n, rfl⟩ := mem_integerThreeHalvesIntervals.mp hU
  refine ⟨integerShiftedInterval n, ?_,
    integerThreeHalvesInterval_subset_integerShiftedInterval n⟩
  exact mem_integerLengthTwoIntervals.mpr ⟨n, rfl⟩

/-- The third conclusion of Exercise 39.4: the collection of real-indexed
intervals of length `3 / 2` does not refine the collection of integer-indexed
intervals of length two. -/
theorem not_isRefinement_realThreeHalvesIntervals_integerLengthTwoIntervals :
    ¬ IsRefinement realThreeHalvesIntervals integerLengthTwoIntervals := by
  intro hRefinement
  -- Apply refinement to the fixed interval whose endpoints straddle the integer grid.
  have hSource : Set.Ioo (3 / 4 : ℝ) (3 / 4 + 3 / 2) ∈ realThreeHalvesIntervals :=
    mem_realThreeHalvesIntervals.mpr ⟨3 / 4, rfl⟩
  obtain ⟨U, hU, hSubset⟩ := hRefinement.subset_of_mem hSource
  obtain ⟨n, hn⟩ := mem_integerLengthTwoIntervals.mp hU
  rw [← hn] at hSubset
  exact realThreeHalvesInterval_threeFourths_not_subset_integerShiftedInterval n hSubset

/-- Exercise 39.4: the collections `realUnitIntervals` and
`integerThreeHalvesIntervals` refine `integerLengthTwoIntervals`, while
`realThreeHalvesIntervals` does not. -/
theorem refinementClassification_integerLengthTwoIntervals :
    IsRefinement realUnitIntervals integerLengthTwoIntervals ∧
      IsRefinement integerThreeHalvesIntervals integerLengthTwoIntervals ∧
        ¬ IsRefinement realThreeHalvesIntervals integerLengthTwoIntervals := by
  -- Package the three component conclusions into the complete exercise answer.
  exact ⟨inferInstance, inferInstance,
    not_isRefinement_realThreeHalvesIntervals_integerLengthTwoIntervals⟩
