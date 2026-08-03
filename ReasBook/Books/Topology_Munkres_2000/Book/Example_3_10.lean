module

public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Basic

open Set

public section

noncomputable section

/-- The ordered subset `{0} ∪ (1, 2)` of `ℝ` from Example 3.10. -/
def isolatedZeroInterval : Set ℝ := {0} ∪ Ioo 1 2

/-- The real-valued formula that fixes `0` and subtracts `1` on `(1, 2)`. -/
@[expose]
def isolatedZeroIntervalToUnitValue (x : ℝ) : ℝ :=
  if x = 0 then 0 else x - 1

/-- The formula `isolatedZeroIntervalToUnitValue` takes values in `[0, 1)` on
`isolatedZeroInterval`. -/
theorem isolatedZeroIntervalToUnitValue_mem (x : isolatedZeroInterval) :
    isolatedZeroIntervalToUnitValue x ∈ Ico (0 : ℝ) 1 := by
  -- Split the source membership into the isolated point and the open interval.
  have hx : (x : ℝ) = 0 ∨ 1 < (x : ℝ) ∧ (x : ℝ) < 2 := by
    simpa only [isolatedZeroInterval, mem_union, mem_singleton_iff, mem_Ioo] using x.property
  by_cases hx0 : (x : ℝ) = 0
  · -- At the isolated point, the forward formula is exactly zero.
    simp only [isolatedZeroIntervalToUnitValue, hx0, if_pos, mem_Ico]
    constructor
    · exact le_rfl
    · exact zero_lt_one
  · -- Every remaining source point lies in `(1, 2)`, so subtraction lands in `[0, 1)`.
    rcases hx with hx | hx
    · exact (hx0 hx).elim
    · simp only [isolatedZeroIntervalToUnitValue, hx0, mem_Ico]
      constructor
      · exact sub_nonneg.mpr (le_of_lt hx.1)
      · exact sub_lt_iff_lt_add.mpr (by simpa only [one_add_one_eq_two] using hx.2)

/-- The correspondence from `{0} ∪ (1, 2)` to `[0, 1)` that fixes `0` and subtracts `1`
on `(1, 2)`. -/
@[expose]
def isolatedZeroIntervalToUnit (x : isolatedZeroInterval) : Set.Ico (0 : ℝ) 1 :=
  ⟨isolatedZeroIntervalToUnitValue x, isolatedZeroIntervalToUnitValue_mem x⟩

/-- The real-valued inverse formula that fixes `0` and adds `1` to positive points. -/
@[expose]
def unitToIsolatedZeroIntervalValue (y : ℝ) : ℝ :=
  if y = 0 then 0 else y + 1

/-- The inverse formula takes values in `{0} ∪ (1, 2)` on `[0, 1)`. -/
theorem unitToIsolatedZeroIntervalValue_mem (y : Set.Ico (0 : ℝ) 1) :
    unitToIsolatedZeroIntervalValue y ∈ isolatedZeroInterval := by
  -- Normalize the target set and split according to the inverse formula's branch.
  rw [isolatedZeroInterval, mem_union, mem_singleton_iff, mem_Ioo]
  by_cases hy0 : (y : ℝ) = 0
  · -- Zero is sent back to the isolated zero.
    left
    simp only [unitToIsolatedZeroIntervalValue, hy0, if_pos]
  · -- A nonzero point of `[0, 1)` is positive, so adding one lands in `(1, 2)`.
    right
    have hypos : 0 < (y : ℝ) := lt_of_le_of_ne y.property.1 (Ne.symm hy0)
    simp only [unitToIsolatedZeroIntervalValue]
    rw [if_neg hy0]
    constructor
    · simpa only [add_comm, zero_add] using add_lt_add_right hypos 1
    · simpa only [add_comm, one_add_one_eq_two] using add_lt_add_right y.property.2 1

/-- The correspondence from `[0, 1)` to `{0} ∪ (1, 2)` that fixes `0` and adds `1`
to positive points. -/
@[expose]
def unitToIsolatedZeroInterval (y : Set.Ico (0 : ℝ) 1) : isolatedZeroInterval :=
  ⟨unitToIsolatedZeroIntervalValue y, unitToIsolatedZeroIntervalValue_mem y⟩

/-- The inverse formula is a left inverse of `isolatedZeroIntervalToUnit`. -/
theorem unitToIsolatedZeroInterval_leftInverse :
    Function.LeftInverse unitToIsolatedZeroInterval isolatedZeroIntervalToUnit := by
  intro x
  -- Subtype extensionality reduces the inverse identity to the two real formulas.
  apply Subtype.ext
  by_cases hx0 : (x : ℝ) = 0
  · -- Both maps fix the isolated point.
    simp only [unitToIsolatedZeroInterval, isolatedZeroIntervalToUnit,
      unitToIsolatedZeroIntervalValue, isolatedZeroIntervalToUnitValue, hx0, if_pos]
  · -- On `(1, 2)`, subtraction by one is nonzero and addition restores the point.
    have hx : (x : ℝ) = 0 ∨ 1 < (x : ℝ) ∧ (x : ℝ) < 2 := by
      simpa only [isolatedZeroInterval, mem_union, mem_singleton_iff, mem_Ioo] using x.property
    rcases hx with hx | hx
    · exact (hx0 hx).elim
    · have hxsub : (x : ℝ) - 1 ≠ 0 := by
        exact ne_of_gt (sub_pos.mpr hx.1)
      simp only [unitToIsolatedZeroInterval, isolatedZeroIntervalToUnit,
        unitToIsolatedZeroIntervalValue, isolatedZeroIntervalToUnitValue]
      simp [hx0, hxsub]

/-- The inverse formula is a right inverse of `isolatedZeroIntervalToUnit`. -/
theorem unitToIsolatedZeroInterval_rightInverse :
    Function.RightInverse unitToIsolatedZeroInterval isolatedZeroIntervalToUnit := by
  intro y
  -- Again, subtype extensionality leaves only the piecewise real-valued calculation.
  apply Subtype.ext
  by_cases hy0 : (y : ℝ) = 0
  · -- Both maps fix zero.
    simp only [isolatedZeroIntervalToUnit, unitToIsolatedZeroInterval,
      isolatedZeroIntervalToUnitValue, unitToIsolatedZeroIntervalValue, hy0, if_pos]
  · -- Adding one is nonzero, and subtracting one returns the original point.
    have hyplus : (y : ℝ) + 1 ≠ 0 := by
      exact ne_of_gt (add_pos_of_nonneg_of_pos y.property.1 zero_lt_one)
    simp only [isolatedZeroIntervalToUnit, unitToIsolatedZeroInterval,
      isolatedZeroIntervalToUnitValue, unitToIsolatedZeroIntervalValue]
    simp [hy0, hyplus]

/-- The correspondence fixing `0` and sending each `x ∈ (1, 2)` to `x - 1` is strictly
order-preserving from `{0} ∪ (1, 2)` to `[0, 1)`. -/
theorem isolatedZeroIntervalToUnit_strictMono :
    StrictMono isolatedZeroIntervalToUnit := by
  intro x y hxy
  -- Decompose both source points into the isolated point or the open interval.
  have hx : (x : ℝ) = 0 ∨ 1 < (x : ℝ) ∧ (x : ℝ) < 2 := by
    simpa only [isolatedZeroInterval, mem_union, mem_singleton_iff, mem_Ioo] using x.property
  have hy : (y : ℝ) = 0 ∨ 1 < (y : ℝ) ∧ (y : ℝ) < 2 := by
    simpa only [isolatedZeroInterval, mem_union, mem_singleton_iff, mem_Ioo] using y.property
  rcases hx with hx0 | hxI
  · rcases hy with hy0 | hyI
    · -- Two copies of the isolated point cannot be strictly ordered.
      have hxy' : (x : ℝ) < (y : ℝ) := hxy
      rw [hx0, hy0] at hxy'
      exact (lt_irrefl 0 hxy').elim
    · -- Zero maps below every translated point from `(1, 2)`.
      simp only [isolatedZeroIntervalToUnit, isolatedZeroIntervalToUnitValue, hx0, if_pos]
      have hy0 : (y : ℝ) ≠ 0 := by
        exact ne_of_gt (lt_trans zero_lt_one hyI.1)
      simp only [hy0]
      exact sub_pos.mpr hyI.1
  · rcases hy with hy0 | hyI
    · -- A point of `(1, 2)` cannot lie below the isolated zero.
      have hxy' : (x : ℝ) < (y : ℝ) := hxy
      rw [hy0] at hxy'
      exact (lt_asymm (lt_trans zero_lt_one hxI.1) hxy').elim
    · -- Translation by `-1` preserves strict order on the open interval.
      have hx0 : (x : ℝ) ≠ 0 := by
        exact ne_of_gt (lt_trans zero_lt_one hxI.1)
      have hy0 : (y : ℝ) ≠ 0 := by
        exact ne_of_gt (lt_trans zero_lt_one hyI.1)
      simp only [isolatedZeroIntervalToUnit, isolatedZeroIntervalToUnitValue, hx0, hy0,
        ]
      have hxy' : (x : ℝ) < (y : ℝ) := hxy
      exact sub_lt_sub_right hxy' 1

/-- The correspondence from `{0} ∪ (1, 2)` to `[0, 1)` is bijective. -/
theorem isolatedZeroIntervalToUnit_bijective :
    Function.Bijective isolatedZeroIntervalToUnit :=
  ⟨isolatedZeroIntervalToUnit_strictMono.injective,
    unitToIsolatedZeroInterval_rightInverse.surjective⟩

/-- Example 3.10: The order isomorphism from `{0} ∪ (1, 2)` to `[0, 1)` fixes `0` and
subtracts `1` on `(1, 2)`. -/
@[expose]
def isolatedZeroIntervalOrderIso : isolatedZeroInterval ≃o Set.Ico (0 : ℝ) 1 where
  toEquiv :=
    { toFun := isolatedZeroIntervalToUnit
      invFun := unitToIsolatedZeroInterval
      left_inv := unitToIsolatedZeroInterval_leftInverse
      right_inv := unitToIsolatedZeroInterval_rightInverse }
  map_rel_iff' := isolatedZeroIntervalToUnit_strictMono.le_iff_le

/-- The forward map of `isolatedZeroIntervalOrderIso` is the stated piecewise formula. -/
@[simp]
theorem isolatedZeroIntervalOrderIso_apply (x : isolatedZeroInterval) :
    isolatedZeroIntervalOrderIso x = isolatedZeroIntervalToUnitValue x := rfl

/-- The inverse map of `isolatedZeroIntervalOrderIso` is the stated piecewise
correspondence from `[0, 1)` to `{0} ∪ (1, 2)`. -/
@[simp]
theorem isolatedZeroIntervalOrderIso_symm_apply (y : Set.Ico (0 : ℝ) 1) :
    isolatedZeroIntervalOrderIso.symm y = unitToIsolatedZeroInterval y := rfl
