import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- The Fourier character sends `0` to the circle basepoint `1`. -/
@[simp] theorem fourierChar_zero_eq_one : Real.fourierChar (0 : ℝ) = (1 : Circle) := by
  simp

/-- The Fourier character sends every integer to the circle basepoint `1`. -/
theorem fourierChar_int_eq_one (n : ℤ) : Real.fourierChar (n : ℝ) = (1 : Circle) := by
  simpa [Real.fourierChar_apply', mul_assoc] using Circle.exp_two_pi_mul_int n

/-- Construction 1.5.3: for each integer `n`, the standard loop on `S¹` based at `1` is the
image of the straight segment `0 ⟶ n` in `ℝ` under `Real.fourierChar`, equivalently the path
`s ↦ e^{2πins}`. -/
def standardLoop (n : ℤ) : Path (1 : Circle) 1 :=
  ((Path.segment (0 : ℝ) n).map Real.continuous_fourierChar).cast
    fourierChar_zero_eq_one.symm (fourierChar_int_eq_one n).symm

/-- The standard loop is the Fourier-character image of the straight segment `0 ⟶ n`. -/
theorem standardLoop_eq_segment_map_fourierChar (n : ℤ) :
    standardLoop n =
      ((Path.segment (0 : ℝ) n).map Real.continuous_fourierChar).cast
        fourierChar_zero_eq_one.symm (fourierChar_int_eq_one n).symm :=
  rfl

/-- Evaluating the standard loop gives the expected exponential formula on the unit interval. -/
@[simp] theorem standardLoop_apply (n : ℤ) (s : unitInterval) :
    standardLoop n s = Circle.exp (2 * Real.pi * (n : ℝ) * (s : ℝ)) := by
  rw [standardLoop_eq_segment_map_fourierChar, Path.cast_coe, Path.map_coe, Function.comp_apply,
    Path.segment_apply, Real.fourierChar_apply']
  rw [AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]
  congr 1
  ring
