import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Construction_1_5_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- The linear lift `f̃_n` of the standard loop is the path `s ↦ n * s` from `0` to `n` in `ℝ`.
This is the canonical straight-line path `Path.segment 0 n`. -/
def standardLoopLift (n : ℤ) : Path (0 : ℝ) n :=
  Path.segment (0 : ℝ) n

/-- Evaluating the lifted standard loop gives the formula `f̃_n(s) = n * s`. -/
-- Proof sketch: `Path.segment` is given by the affine line map; for endpoints `0` and `n`, this
-- simplifies to multiplication by `n`.
@[simp] theorem standardLoopLift_apply (n : ℤ) (s : unitInterval) :
    standardLoopLift n s = (n : ℝ) * (s : ℝ) := by
  rw [standardLoopLift, Path.segment_apply, AffineMap.lineMap_apply_module]
  simp
  ring

/-- Construction 1.5.5: the standard loop `f_n` is the image of its linear lift under
`Real.fourierChar : ℝ → S¹`, with the endpoints recast using
`Real.fourierChar 0 = 1 = Real.fourierChar n`. -/
theorem standardLoop_eq_standardLoopLift_map_fourierChar (n : ℤ) :
    standardLoop n =
      ((standardLoopLift n).map Real.continuous_fourierChar).cast
        fourierChar_zero_eq_one.symm (fourierChar_int_eq_one n).symm := by
  simpa [standardLoopLift] using standardLoop_eq_segment_map_fourierChar n

/-- Construction 1.5.5: the standard loop `f_n` factors through the canonical covering map
`Real.fourierChar : ℝ → S¹` by the lift `f̃_n(s) = n * s`. -/
-- Proof sketch: combine `standardLoop_apply` from Construction 1.5.3 with
-- `standardLoopLift_apply`, then identify the resulting expression with `Real.fourierChar`.
theorem standardLoop_factors_through_fourierChar (n : ℤ) (s : unitInterval) :
    standardLoop n s = Real.fourierChar (standardLoopLift n s) := by
  rw [standardLoop_apply, standardLoopLift_apply, Real.fourierChar_apply']
  ring_nf

/-- In textbook notation, the factorization of `f_n` through the covering map reads
`f_n(s) = Circle.exp (2 * π * f̃_n(s))`. -/
theorem standardLoop_factors_through_circle_exp (n : ℤ) (s : unitInterval) :
    standardLoop n s = Circle.exp (2 * Real.pi * standardLoopLift n s) := by
  rw [standardLoop_factors_through_fourierChar]
  simp [Real.fourierChar_apply']
