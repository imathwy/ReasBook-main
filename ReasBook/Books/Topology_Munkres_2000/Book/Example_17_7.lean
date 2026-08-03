module

public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered
import Topology_Munkres_2000.Book.Theorem_17_4

public section

open Set

/-- The subset `Y = (0, 1]` of `ℝ`, regarded as a subspace. -/
def halfOpenUnitInterval : Set ℝ := Ioc 0 1

/-- The interval `A = (0, 1 / 2)` in `ℝ`. -/
def lowerHalfInterval : Set ℝ := Ioo 0 (1 / 2)

/-- The interval `A = (0, 1 / 2)` regarded as a subset of the subspace `Y = (0, 1]`. -/
def lowerHalfInUnitInterval : Set halfOpenUnitInterval :=
  Subtype.val ⁻¹' lowerHalfInterval

/-- Helper for Example 17.7: the closure in `ℝ` of `A = (0, 1 / 2)` is `[0, 1 / 2]`. -/
theorem closure_lowerHalfInReal :
    closure lowerHalfInterval = Icc (0 : ℝ) (1 / 2) := by
  -- Compute the ambient closure using the standard closure formula for open intervals.
  unfold lowerHalfInterval
  rw [closure_Ioo]
  norm_num

/-- Helper for Example 17.7: the ambient image of `A` is the real interval `(0, 1 / 2)`. -/
lemma image_lowerHalfInUnitInterval :
    Subtype.val '' lowerHalfInUnitInterval = lowerHalfInterval := by
  -- The forward inclusion simply forgets the proof that the point belongs to the subspace.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    -- The bound `x < 1 / 2` places `x` in the larger interval `(0, 1]`.
    have hxY : x ∈ halfOpenUnitInterval := by
      unfold halfOpenUnitInterval
      unfold lowerHalfInterval at hx
      constructor
      · exact hx.1
      · linarith [hx.2]
    exact ⟨⟨x, hxY⟩, hx, rfl⟩

/-- Helper for Example 17.7: intersecting `[0, 1 / 2]` with `(0, 1]` gives `(0, 1 / 2]`. -/
lemma closedLowerHalf_inter_halfOpenUnit :
    Icc (0 : ℝ) (1 / 2) ∩ halfOpenUnitInterval = Ioc (0 : ℝ) (1 / 2) := by
  -- Normalize membership in the three intervals and retain exactly positivity and the half bound.
  ext x
  unfold halfOpenUnitInterval
  simp only [mem_inter_iff, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨⟨_, hxHalf⟩, hxPositive, _⟩
    exact ⟨hxPositive, hxHalf⟩
  · rintro ⟨hxPositive, hxHalf⟩
    have hxUnit : x ≤ (1 : ℝ) := by
      linarith
    constructor
    · exact ⟨le_of_lt hxPositive, hxHalf⟩
    · exact ⟨hxPositive, hxUnit⟩

/-- The image in `ℝ` of the closure of `A` in `Y = (0, 1]` is `(0, 1 / 2]`. -/
theorem image_closure_lowerHalfInSubspace :
    Subtype.val '' closure lowerHalfInUnitInterval = Ioc (0 : ℝ) (1 / 2) := by
  -- The subspace closure is the ambient closure intersected with the subspace.
  rw [image_closure_eq_inter, image_lowerHalfInUnitInterval, closure_lowerHalfInReal,
    closedLowerHalf_inter_halfOpenUnit]

/-- Example 17.7 (2): The closure of `A = (0, 1 / 2)` in the subspace
`Y = (0, 1]` is `(0, 1 / 2]`, regarded as a subset of `Y`. -/
theorem closure_lowerHalfInSubspace :
    closure lowerHalfInUnitInterval = Subtype.val ⁻¹' Ioc (0 : ℝ) (1 / 2) := by
  -- Compare the two subtype sets through the injective ambient image operation.
  apply Subtype.val_injective.image_injective
  rw [image_closure_lowerHalfInSubspace, image_preimage_eq_inter_range, Subtype.range_coe]
  -- The interval `(0, 1 / 2]` already lies in the subspace `(0, 1]`.
  ext x
  unfold halfOpenUnitInterval
  simp only [mem_Ioc, mem_inter_iff]
  constructor
  · intro hx
    have hxUnit : x ≤ (1 : ℝ) := by
      linarith [hx.2]
    exact ⟨hx, hx.1, hxUnit⟩
  · intro hx
    exact hx.1
