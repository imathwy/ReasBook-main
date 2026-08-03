module

public import Topology_Munkres_2000.Book.Example_38_2.Compactification

public section

open Set
open OpenUnitInterval

/- Example 38.2 (1): The closed unit interval is a compactification of the open unit interval. -/
#check closedUnitIntervalCompactification

/-- Helper for Example 38.2: the compactification embedding has exactly the open interval
as its range inside the closed interval. -/
lemma OpenUnitInterval.range_closedUnitIntervalCompactification :
    Set.range closedUnitIntervalCompactification =
      {y : Icc (0 : ℝ) 1 | (y : ℝ) ∈ Ioo (0 : ℝ) 1} := by
  -- First identify the compactification map with the canonical interval inclusion.
  have hmap :
      (closedUnitIntervalCompactification : Ioo (0 : ℝ) 1 → Icc (0 : ℝ) 1) =
        UnitInterval.openInClosed := by
    funext x
    exact closedUnitIntervalCompactification_apply x
  -- The standard range formula for a subtype inclusion now gives the claimed set.
  calc
    Set.range closedUnitIntervalCompactification = Set.range UnitInterval.openInClosed :=
      congrArg (fun f ↦ Set.range f) hmap
    _ = {y : Icc (0 : ℝ) 1 | (y : ℝ) ∈ Ioo (0 : ℝ) 1} := by
      simpa only [UnitInterval.openInClosed] using
        Set.range_inclusion UnitInterval.open_subset_closed

/-- Example 38.2 (2): The remainder of the closed-interval compactification consists exactly
of its two endpoints. -/
theorem OpenUnitInterval.closedUnitIntervalCompactification_remainder_iff
    (y : Icc (0 : ℝ) 1) :
    y ∉ Set.range closedUnitIntervalCompactification ↔ y.1 = 0 ∨ y.1 = 1 := by
  -- Read the range description pointwise, avoiding any unfolding of the compactification carrier.
  have hrange :
      y ∈ Set.range closedUnitIntervalCompactification ↔ (y : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    Set.ext_iff.mp range_closedUnitIntervalCompactification y
  constructor
  · intro hy
    -- Every point of the closed interval is an endpoint or lies in its interior.
    rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc y.property with hy0 | hy1 | hinterior
    · exact Or.inl hy0
    · exact Or.inr hy1
    · exact (hy (hrange.mpr hinterior)).elim
  · -- Neither endpoint belongs to the corresponding open interval.
    intro hy hyrange
    have hinterior := hrange.mp hyrange
    rcases hy with hy0 | hy1
    · rw [hy0] at hinterior
      exact Set.left_notMem_Ioo hinterior
    · rw [hy1] at hinterior
      exact Set.right_notMem_Ioo hinterior


end
