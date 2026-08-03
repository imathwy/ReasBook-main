module

public import Topology_Munkres_2000.Book.Exercise_54_3.Concatenation
public import Topology_Munkres_2000.Book.Example_53_6.Polar

@[expose] public section

noncomputable section

open Set unitInterval

namespace Circle

/-- Helper for Exercise 54.4: translating the angular coordinate by an integer leaves
`turnExp` unchanged. -/
theorem turnExp_int_add (n : ℤ) (x : ℝ) :
    turnExp ((n : ℝ) + x) = turnExp x := by
  -- Split the exponential at the integer shift, whose first factor is one.
  have integerFactor : Circle.exp (2 * Real.pi * (n : ℝ)) = 1 := by
    simpa only [turnExp_eq_exp_scale] using turnExp_int n
  rw [turnExp_eq_exp_scale]
  calc
    Circle.exp (2 * Real.pi * ((n : ℝ) + x)) =
        Circle.exp (2 * Real.pi * (n : ℝ) + 2 * Real.pi * x) := by
      congr 1
      ring
    _ = Circle.exp (2 * Real.pi * (n : ℝ)) * Circle.exp (2 * Real.pi * x) :=
      Circle.exp_add _ _
    _ = Circle.exp (2 * Real.pi * x) := by rw [integerFactor, one_mul]

end Circle

namespace PolarLift

/-- The inner endpoint of the radial segment and the spiral. -/
def one : {z : ℂ // z ≠ 0} := ⟨1, one_ne_zero⟩

/-- The outer endpoint of the radial segment and the spiral. -/
def two : {z : ℂ // z ≠ 0} := ⟨2, two_ne_zero⟩

/-- Helper for Exercise 54.4: one is a positive radius. -/
lemma one_mem_Ioi : (1 : ℝ) ∈ Set.Ioi 0 := by
  -- Normalize membership in the positive-real interval.
  norm_num

/-- Helper for Exercise 54.4: two is a positive radius. -/
lemma two_mem_Ioi : (2 : ℝ) ∈ Set.Ioi 0 := by
  -- Normalize membership in the positive-real interval.
  norm_num

/-- The point over the inner endpoint on the sheet indexed by `n`. -/
def sheetOne (n : ℤ) : ℝ × Set.Ioi (0 : ℝ) := ((n : ℝ), ⟨1, one_mem_Ioi⟩)

/-- The point over the outer endpoint on the sheet indexed by `n`. -/
def sheetTwo (n : ℤ) : ℝ × Set.Ioi (0 : ℝ) := ((n : ℝ), ⟨2, two_mem_Ioi⟩)

/-- Helper for Exercise 54.4: the radial segment has positive radius on `unitInterval`. -/
lemma segmentRadius_pos (t : unitInterval) : 0 < 2 - (t : ℝ) := by
  -- The unit-interval upper bound keeps the radius at least one.
  linarith [t.2.2]

/-- Helper for Exercise 54.4: every point in the displayed radial segment is nonzero. -/
lemma segmentValue_ne_zero (t : unitInterval) :
    ((2 - (t : ℝ) : ℝ) : ℂ) ≠ 0 := by
  -- Embed the strictly positive real radius into the complex plane.
  exact Complex.ofReal_ne_zero.mpr (segmentRadius_pos t).ne'

/-- Helper for Exercise 54.4: the displayed radial parametrization is continuous. -/
lemma continuous_segmentParam :
    Continuous (fun t : unitInterval ↦
      (⟨((2 - (t : ℝ) : ℝ) : ℂ), segmentValue_ne_zero t⟩ : {z : ℂ // z ≠ 0})) := by
  -- Continuity reduces to the affine real coordinate after forming the subtype.
  apply Continuous.subtype_mk
  fun_prop

/-- Helper for Exercise 54.4: the radial parametrization runs from `two` to `one`. -/
lemma segmentParamEndpoints :
    (⟨((2 - ((0 : unitInterval) : ℝ) : ℝ) : ℂ), segmentValue_ne_zero 0⟩ :
        {z : ℂ // z ≠ 0}) = two ∧
      (⟨((2 - ((1 : unitInterval) : ℝ) : ℝ) : ℂ), segmentValue_ne_zero 1⟩ :
        {z : ℂ // z ≠ 0}) = one := by
  -- Evaluate the affine radius at the two endpoints.
  constructor
  · apply Subtype.ext
    norm_num [two]
  · apply Subtype.ext
    norm_num [one]

/-- The radial path `f(t) = (2 - t, 0)` from radius two to radius one. -/
def segment : Path two one where
  toFun t := ⟨((2 - (t : ℝ) : ℝ) : ℂ), segmentValue_ne_zero t⟩
  continuous_toFun := continuous_segmentParam
  source' := segmentParamEndpoints.1
  target' := segmentParamEndpoints.2

/-- The radial path has value `2 - t` on the positive real axis. -/
@[simp]
theorem segment_apply (t : unitInterval) :
    (segment t : ℂ) = ((2 - (t : ℝ) : ℝ) : ℂ) := rfl

/-- Helper for Exercise 54.4: the outward spiral has positive radius on `unitInterval`. -/
lemma spiralRadius_pos (t : unitInterval) : 0 < 1 + (t : ℝ) := by
  -- The unit-interval lower bound makes the radius at least one.
  linarith [t.2.1]

/-- Helper for Exercise 54.4: the positive-polar spiral parametrization is continuous. -/
lemma continuous_spiralParam :
    Continuous (fun t : unitInterval ↦
      Complex.polarForward
        (Circle.turnExp (t : ℝ), ⟨1 + (t : ℝ), spiralRadius_pos t⟩)) := by
  -- Combine continuity of the angular and radial polar coordinates.
  apply Complex.continuous_polarForward.comp
  apply Continuous.prodMk
  · rw [Circle.turnExp_eq_exp_scale]
    fun_prop
  · apply Continuous.subtype_mk
    fun_prop

/-- Helper for Exercise 54.4: the positive-polar spiral runs from `one` to `two`. -/
lemma spiralParamEndpoints :
    Complex.polarForward
        (Circle.turnExp ((0 : unitInterval) : ℝ),
          ⟨1 + ((0 : unitInterval) : ℝ), spiralRadius_pos 0⟩) = one ∧
      Complex.polarForward
        (Circle.turnExp ((1 : unitInterval) : ℝ),
          ⟨1 + ((1 : unitInterval) : ℝ), spiralRadius_pos 1⟩) = two := by
  -- At both endpoints the angular factor is one, so only the radius remains.
  constructor
  · apply Subtype.ext
    norm_num [Complex.polarForward, Complex.polarForwardValue, one, Circle.turnExp_zero]
  · apply Subtype.ext
    norm_num [Complex.polarForward, Complex.polarForwardValue, two, Circle.turnExp_one]

/-- The outward spiral
`g(t) = ((1 + t) cos (2πt), (1 + t) sin (2πt))`. -/
def spiral : Path one two where
  toFun t := Complex.polarForward
    (Circle.turnExp (t : ℝ), ⟨1 + (t : ℝ), spiralRadius_pos t⟩)
  continuous_toFun := continuous_spiralParam
  source' := spiralParamEndpoints.1
  target' := spiralParamEndpoints.2

/-- The outward spiral has the stated polar-coordinate formula. -/
@[simp]
theorem spiral_apply (t : unitInterval) :
    (spiral t : ℂ) =
      ((1 + (t : ℝ) : ℝ) : ℂ) * (Circle.turnExp (t : ℝ) : ℂ) := rfl

/-- The outward spiral has the stated cosine-sine coordinate formula. -/
theorem spiral_coe_apply (t : unitInterval) :
    (spiral t : ℂ) = ((1 + (t : ℝ) : ℝ) : ℂ) *
      (Real.cos (2 * Real.pi * (t : ℝ)) +
        Real.sin (2 * Real.pi * (t : ℝ)) * Complex.I) := by
  -- Replace the angular factor by its cosine-sine coordinate formula.
  rw [spiral_apply, Circle.coe_turnExp]

/-- The concatenated path `h = f * g`. -/
def concat : Path two two := segment.trans spiral

/-- Helper for Exercise 54.4: the radial lift parametrization is continuous. -/
lemma continuous_segmentLiftParam (n : ℤ) :
    Continuous (fun t : unitInterval ↦
      (((n : ℝ), ⟨2 - (t : ℝ), segmentRadius_pos t⟩) :
        ℝ × Set.Ioi (0 : ℝ))) := by
  -- The sheet coordinate is constant and the radius is affine.
  apply Continuous.prodMk
  · fun_prop
  · apply Continuous.subtype_mk
    fun_prop

/-- Helper for Exercise 54.4: the radial lift stays on sheet `n` at both endpoints. -/
lemma segmentLiftParamEndpoints (n : ℤ) :
    ((n : ℝ), ⟨2 - ((0 : unitInterval) : ℝ), segmentRadius_pos 0⟩) = sheetTwo n ∧
      ((n : ℝ), ⟨2 - ((1 : unitInterval) : ℝ), segmentRadius_pos 1⟩) = sheetOne n := by
  -- Evaluate both product coordinates at zero and one.
  constructor
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      norm_num [sheetTwo]
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      norm_num [sheetOne]

/-- The constant-angle lift of the radial path on the sheet indexed by `n`. -/
def segmentLift (n : ℤ) : Path (sheetTwo n) (sheetOne n) where
  toFun t := ((n : ℝ), ⟨2 - (t : ℝ), segmentRadius_pos t⟩)
  continuous_toFun := continuous_segmentLiftParam n
  source' := (segmentLiftParamEndpoints n).1
  target' := (segmentLiftParamEndpoints n).2

/-- The angular coordinate of the radial lift is constant. -/
@[simp]
theorem segmentLift_fst (n : ℤ) (t : unitInterval) :
    (segmentLift n t).1 = n := rfl

/-- The radial coordinate of the radial lift is `2 - t`. -/
@[simp]
theorem segmentLift_snd (n : ℤ) (t : unitInterval) :
    (segmentLift n t).2.1 = 2 - (t : ℝ) := rfl

/-- Helper for Exercise 54.4: the spiral lift parametrization is continuous. -/
lemma continuous_spiralLiftParam (n : ℤ) :
    Continuous (fun t : unitInterval ↦
      (((n : ℝ) + (t : ℝ), ⟨1 + (t : ℝ), spiralRadius_pos t⟩) :
        ℝ × Set.Ioi (0 : ℝ))) := by
  -- Both the angular coordinate and radius are affine functions of the parameter.
  apply Continuous.prodMk
  · fun_prop
  · apply Continuous.subtype_mk
    fun_prop

/-- Helper for Exercise 54.4: the spiral lift advances from sheet `n` to sheet `n + 1`. -/
lemma spiralLiftParamEndpoints (n : ℤ) :
    ((n : ℝ) + ((0 : unitInterval) : ℝ),
        ⟨1 + ((0 : unitInterval) : ℝ), spiralRadius_pos 0⟩) = sheetOne n ∧
      ((n : ℝ) + ((1 : unitInterval) : ℝ),
        ⟨1 + ((1 : unitInterval) : ℝ), spiralRadius_pos 1⟩) = sheetTwo (n + 1) := by
  -- Endpoint arithmetic records the single-sheet increase of the angular coordinate.
  constructor
  · apply Prod.ext
    · norm_num [sheetOne]
    · apply Subtype.ext
      norm_num [sheetOne]
  · apply Prod.ext
    · norm_num [sheetTwo]
    · apply Subtype.ext
      norm_num [sheetTwo]

/-- The lift of the outward spiral whose angle increases from `n` to `n + 1`. -/
def spiralLift (n : ℤ) : Path (sheetOne n) (sheetTwo (n + 1)) where
  toFun t := ((n : ℝ) + (t : ℝ), ⟨1 + (t : ℝ), spiralRadius_pos t⟩)
  continuous_toFun := continuous_spiralLiftParam n
  source' := (spiralLiftParamEndpoints n).1
  target' := (spiralLiftParamEndpoints n).2

/-- The angular coordinate of the spiral lift is `n + t`. -/
@[simp]
theorem spiralLift_fst (n : ℤ) (t : unitInterval) :
    (spiralLift n t).1 = (n : ℝ) + (t : ℝ) := rfl

/-- The radial coordinate of the spiral lift is `1 + t`. -/
@[simp]
theorem spiralLift_snd (n : ℤ) (t : unitInterval) :
    (spiralLift n t).2.1 = 1 + (t : ℝ) := rfl

/-- The concatenation of the explicit radial and spiral lifts. -/
def concatLift (n : ℤ) : Path (sheetTwo n) (sheetTwo (n + 1)) :=
  (segmentLift n).trans (spiralLift n)

/-- Helper for Exercise 54.4: the polar covering sends the radial lift to `segment`. -/
lemma polarTurn_segmentLift (n : ℤ) (t : unitInterval) :
    Complex.polarTurn (segmentLift n t) = segment t := by
  -- Compare punctured-plane points through their underlying complex values.
  apply Subtype.ext
  rw [Complex.coe_polarTurn, segment_apply, segmentLift_snd, segmentLift_fst,
    Circle.turnExp_int]
  exact mul_one _

/-- Helper for Exercise 54.4: the polar covering sends the spiral lift to `spiral`. -/
lemma polarTurn_spiralLift (n : ℤ) (t : unitInterval) :
    Complex.polarTurn (spiralLift n t) = spiral t := by
  -- Remove the integer sheet offset from the angular coordinate.
  apply Subtype.ext
  rw [Complex.coe_polarTurn, spiral_apply, spiralLift_snd, spiralLift_fst,
    Circle.turnExp_int_add]

/-- Exercise 54.4 (1). The path `t ↦ (n, 2 - t)` lifts
`f(t) = (2 - t, 0)`. -/
theorem segmentLift_isLift (n : ℤ) :
    ContinuousMap.IsLift Complex.polarTurn segment.toContinuousMap
      (segmentLift n).toContinuousMap := by
  -- Reduce the lifting equation to the pointwise polar-coordinate computation.
  rw [ContinuousMap.isLift_iff]
  funext t
  exact polarTurn_segmentLift n t

/-- Companion to Exercise 54.4 (2). The path `t ↦ (n + t, 1 + t)` lifts the outward
spiral. -/
theorem spiralLift_isLift (n : ℤ) :
    ContinuousMap.IsLift Complex.polarTurn spiral.toContinuousMap
      (spiralLift n).toContinuousMap := by
  -- Reduce the lifting equation to integer periodicity of the angular coordinate.
  rw [ContinuousMap.isLift_iff]
  funext t
  exact polarTurn_spiralLift n t

/-- Companion to Exercise 54.4 (3). Concatenating the displayed lifts gives a lift of
`h = f * g`. -/
theorem concatLift_isLift (n : ℤ) :
    ContinuousMap.IsLift Complex.polarTurn concat.toContinuousMap
      (concatLift n).toContinuousMap :=
  (segmentLift_isLift n).transPath (spiralLift_isLift n)

end PolarLift
