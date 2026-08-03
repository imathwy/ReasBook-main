module

public import Topology_Munkres_2000.Book.Example_2_2.RealFunctions
public import Mathlib.Analysis.Real.Sqrt

public section

/-- Example 2.4 (1). The image of `Set.Icc 0 1` under `x ↦ 3 * x ^ 2 + 2` is
`Set.Icc 2 5`. -/
theorem quadraticImageUnitInterval :
    shiftedQuadratic '' Set.Icc 0 1 = Set.Icc 2 5 := by
  ext y
  constructor
  · -- Bound every value attained on the unit interval.
    rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_Icc] at hx ⊢
    constructor
    · unfold shiftedQuadratic
      nlinarith [sq_nonneg x]
    · have hxLeftNonneg : 0 ≤ x + 1 := by
        linarith [hx.1]
      have hxRightNonneg : 0 ≤ 1 - x := by
        linarith [hx.2]
      have hproduct : 0 ≤ (x + 1) * (1 - x) :=
        mul_nonneg hxLeftNonneg hxRightNonneg
      unfold shiftedQuadratic
      nlinarith
  · -- Recover a point of the unit interval with the nonnegative square root.
    intro hy
    simp only [Set.mem_Icc] at hy
    have hradicandNonneg : 0 ≤ (y - 2) / 3 := by
      linarith [hy.1]
    have hradicandLeOne : (y - 2) / 3 ≤ 1 := by
      linarith [hy.2]
    refine ⟨√((y - 2) / 3), ?_, ?_⟩
    · simp only [Set.mem_Icc]
      exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr hradicandLeOne⟩
    · unfold shiftedQuadratic
      rw [Real.sq_sqrt hradicandNonneg]
      ring

/-- For `f x = 3 * x ^ 2 + 2`, the preimage of the image of `Set.Icc 0 1`
equals the preimage of `Set.Icc 2 5`. -/
theorem quadraticPreimageImageUnitInterval :
    shiftedQuadratic ⁻¹' (shiftedQuadratic '' Set.Icc 0 1) =
      shiftedQuadratic ⁻¹' Set.Icc 2 5 := by
  rw [quadraticImageUnitInterval]

/-- Example 2.4 (2). For `f x = 3 * x ^ 2 + 2`, the preimage of
`Set.Icc 2 5` is `Set.Icc (-1) 1`. -/
theorem quadraticPreimageValueInterval :
    shiftedQuadratic ⁻¹' Set.Icc 2 5 = Set.Icc (-1) 1 := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Icc, shiftedQuadratic]
  constructor
  · -- The upper value bound forces the input between the two roots.
    intro hx
    constructor
    · nlinarith [sq_nonneg (x + 1)]
    · nlinarith [sq_nonneg (x - 1)]
  · -- Interval bounds control the square, while its nonnegativity gives the lower value bound.
    intro hx
    have hxLeftNonneg : 0 ≤ x + 1 := by
      linarith [hx.1]
    have hxRightNonneg : 0 ≤ 1 - x := by
      linarith [hx.2]
    have hproduct : 0 ≤ (x + 1) * (1 - x) :=
      mul_nonneg hxLeftNonneg hxRightNonneg
    constructor
    · nlinarith [sq_nonneg x]
    · nlinarith

/-- Example 2.4 (3). The preimage of `Set.Icc 0 5` under
`x ↦ 3 * x ^ 2 + 2` is
`Set.Icc (-1) 1`. -/
theorem quadraticPreimageZeroFiveInterval :
    shiftedQuadratic ⁻¹' Set.Icc 0 5 = Set.Icc (-1) 1 := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Icc, shiftedQuadratic]
  constructor
  · -- As before, only the upper value bound is needed to locate the input.
    intro hx
    constructor
    · nlinarith [sq_nonneg (x + 1)]
    · nlinarith [sq_nonneg (x - 1)]
  · -- Inputs in the symmetric interval have square at most one.
    intro hx
    have hxLeftNonneg : 0 ≤ x + 1 := by
      linarith [hx.1]
    have hxRightNonneg : 0 ≤ 1 - x := by
      linarith [hx.2]
    have hproduct : 0 ≤ (x + 1) * (1 - x) :=
      mul_nonneg hxLeftNonneg hxRightNonneg
    constructor
    · nlinarith [sq_nonneg x]
    · nlinarith

/-- For `f x = 3 * x ^ 2 + 2`, the image of the preimage of
`Set.Icc 0 5` equals the image of `Set.Icc (-1) 1`. -/
theorem quadraticImagePreimageInterval :
    shiftedQuadratic '' (shiftedQuadratic ⁻¹' Set.Icc 0 5) =
      shiftedQuadratic '' Set.Icc (-1) 1 := by
  rw [quadraticPreimageZeroFiveInterval]

/-- Example 2.4 (4). For `f x = 3 * x ^ 2 + 2`, the image of
`Set.Icc (-1) 1` is `Set.Icc 2 5`. -/
theorem quadraticImageSymmetricInterval :
    shiftedQuadratic '' Set.Icc (-1) 1 = Set.Icc 2 5 := by
  ext y
  constructor
  · -- Directly bound every value attained on the symmetric interval.
    rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_Icc] at hx ⊢
    have hxLeftNonneg : 0 ≤ x + 1 := by
      linarith [hx.1]
    have hxRightNonneg : 0 ≤ 1 - x := by
      linarith [hx.2]
    have hproduct : 0 ≤ (x + 1) * (1 - x) :=
      mul_nonneg hxLeftNonneg hxRightNonneg
    constructor
    · unfold shiftedQuadratic
      nlinarith [sq_nonneg x]
    · unfold shiftedQuadratic
      nlinarith
  · -- The unit interval already supplies every value in the target interval.
    intro hy
    have hyUnit : y ∈ shiftedQuadratic '' Set.Icc 0 1 := by
      rw [quadraticImageUnitInterval]
      exact hy
    rcases hyUnit with ⟨x, hx, hxy⟩
    refine ⟨x, ?_, hxy⟩
    have hxLower : -1 ≤ x := by
      linarith [hx.1]
    exact ⟨hxLower, hx.2⟩
