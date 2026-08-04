module

public import Topology_Munkres_2000.Book.Definition_66_4.Predicates
public import Topology_Munkres_2000.Book.Example_54_1
public import Topology_Munkres_2000.Book.Theorem_66_2

public section

open unitInterval

namespace PlaneLoop

/- Definition 66.4 (1): A simple plane loop is counterclockwise when its winding number is `1` at
some, hence every, point of its bounded complementary component.
-/
#check IsCounterclockwise

/- Definition 66.4 (2): A simple plane loop is clockwise when its winding number is `-1` at some,
hence every, point of its bounded complementary component.
-/
#check IsClockwise

/-- The standard plane loop traversing the unit circle once in the positive direction. -/
noncomputable def standardLoop : Path (1 : ℂ) 1 :=
  ((Circle.turnPath 1).map continuous_subtype_val).cast rfl
    (congr_arg Subtype.val Circle.turnExp_one).symm

/-- Evaluating the standard plane loop gives the one-turn circle parametrization. -/
@[simp]
theorem standardLoop_apply (s : unitInterval) :
    standardLoop s = (Circle.turnExp (s : ℝ) : ℂ) := by
  rw [standardLoop, Path.cast_coe, Path.map_coe]
  change ((Circle.turnPath 1 s : Circle) : ℂ) = _
  rw [Circle.turnPath_apply, one_mul]

/-- The standard plane loop has the source's cosine-sine formula. -/
theorem standardLoop_apply_cos_sin (s : unitInterval) :
    standardLoop s =
      Real.cos (2 * Real.pi * (s : ℝ)) + Real.sin (2 * Real.pi * (s : ℝ)) * Complex.I :=
  (standardLoop_apply s).trans (Circle.coe_turnExp _)

/-- The standard plane loop is simple. -/
theorem standardLoop_isSimple : standardLoop.toContinuousMap.IsSimpleLoop := by
  -- First record that the path has equal endpoint values.
  rw [ContinuousMap.isSimpleLoop_iff]
  constructor
  · rw [ContinuousMap.isLoop_iff]
    exact standardLoop.source.trans standardLoop.target.symm
  · -- Equal circle values differ by an integral number of turns.
    intro s₁ s₂ heq
    have hexp : Circle.turnExp (s₁ : ℝ) = Circle.turnExp (s₂ : ℝ) := by
      apply Subtype.ext
      simpa only [Path.coe_toContinuousMap, standardLoop_apply] using heq
    rw [Circle.turnExp_eq_exp_scale] at hexp
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp
    have hscale : 2 * Real.pi ≠ 0 := by
      positivity
    have hperiod : (s₁ : ℝ) = (s₂ : ℝ) + (m : ℝ) := by
      apply mul_left_cancel₀ hscale
      calc
        (2 * Real.pi) * (s₁ : ℝ) =
            (2 * Real.pi) * (s₂ : ℝ) + (m : ℝ) * (2 * Real.pi) := hm
        _ = (2 * Real.pi) * ((s₂ : ℝ) + (m : ℝ)) := by ring
    -- The unit-interval bounds leave only the periods `-1`, `0`, and `1`.
    have hmLowerReal : (-1 : ℝ) ≤ (m : ℝ) := by
      linarith [s₁.property.1, s₂.property.2]
    have hmUpperReal : (m : ℝ) ≤ 1 := by
      linarith [s₁.property.2, s₂.property.1]
    have hmLower : (-1 : ℤ) ≤ m := by
      exact_mod_cast hmLowerReal
    have hmUpper : m ≤ (1 : ℤ) := by
      exact_mod_cast hmUpperReal
    have hmAbs : |m| ≤ (1 : ℤ) := by
      exact abs_le.mpr ⟨hmLower, hmUpper⟩
    rcases Int.abs_le_one_iff.mp hmAbs with rfl | rfl | rfl
    · left
      apply Subtype.ext
      simpa only [Int.cast_zero, add_zero] using hperiod
    · right
      right
      norm_num at hperiod
      have hs₁ : (s₁ : ℝ) = 1 := by
        linarith [s₁.property.2, s₂.property.1]
      have hs₂ : (s₂ : ℝ) = 0 := by
        linarith [s₁.property.2, s₂.property.1]
      constructor
      · apply Subtype.ext
        exact hs₁
      · apply Subtype.ext
        exact hs₂
    · right
      left
      norm_num at hperiod
      have hs₁ : (s₁ : ℝ) = 0 := by
        linarith [s₁.property.1, s₂.property.2]
      have hs₂ : (s₂ : ℝ) = 1 := by
        linarith [s₁.property.1, s₂.property.2]
      constructor
      · apply Subtype.ext
        exact hs₁
      · apply Subtype.ext
        exact hs₂

/-- Helper for Definition 66.4: the standard loop avoids the origin. -/
lemma zero_not_mem_range_standardLoop :
    (0 : ℂ) ∉ Set.range standardLoop := by
  -- Taking norms would force the unit-circle value to have norm zero.
  rintro ⟨t, ht⟩
  have hnorm := congrArg norm ht
  simp only [standardLoop_apply, Circle.norm_coe, norm_zero] at hnorm
  norm_num at hnorm

/-- Helper for Definition 66.4: normalization about the origin preserves the standard
circle parametrization. -/
lemma standardLoop_normalizedLoop_apply
    (h_avoid : (0 : ℂ) ∉ Set.range standardLoop) (t : unitInterval) :
    normalizedLoop standardLoop 0 h_avoid t = Circle.turnExp (t : ℝ) := by
  -- On the unit circle, subtracting zero and dividing by the norm changes nothing.
  apply Subtype.ext
  simp only [normalizedLoop_apply, direction_coe, standardLoop_apply, sub_zero,
    Circle.norm_coe, Complex.ofReal_one, div_one]

/-- Helper for Definition 66.4: the angular coordinate of the standard loop is its parameter
modulo one. -/
lemma standardLoop_angularLoop_apply
    (h_avoid : (0 : ℂ) ∉ Set.range standardLoop) (t : unitInterval) :
    angularLoop standardLoop 0 h_avoid t = ((t : ℝ) : UnitAddCircle) := by
  -- Compare both angular coordinates after applying the circle homeomorphism.
  apply (AddCircle.homeomorphCircle one_ne_zero).injective
  calc
    AddCircle.homeomorphCircle one_ne_zero
        (angularLoop standardLoop 0 h_avoid t) =
        normalizedLoop standardLoop 0 h_avoid t :=
      homeomorphCircle_angularLoop_apply standardLoop 0 h_avoid t
    _ = Circle.turnExp (t : ℝ) := standardLoop_normalizedLoop_apply h_avoid t
    _ = AddCircle.homeomorphCircle one_ne_zero ((t : ℝ) : UnitAddCircle) := by
      rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk,
        Circle.turnExp_eq_exp_scale, div_one]

/-- Helper for Definition 66.4: the winding number of the standard loop about the origin is
one. -/
lemma windingNumber_standardLoop_zero :
    windingNumber standardLoop 0 zero_not_mem_range_standardLoop = 1 := by
  -- The linear path from `0` to `1` is an explicit lift of the angular loop.
  have hprojection (t : unitInterval) :
      (((Circle.turnLift 1).toContinuousMap t : ℝ) : UnitAddCircle) =
        angularLoop standardLoop 0 zero_not_mem_range_standardLoop t := by
    simp only [Path.coe_toContinuousMap, Circle.turnLift_apply, one_mul,
      standardLoop_angularLoop_apply]
  have hdisplacement := windingNumber_spec_angularLoop standardLoop 0
    zero_not_mem_range_standardLoop (Circle.turnLift 1).toContinuousMap hprojection
  -- Its endpoint displacement is exactly one turn.
  simp only [Path.coe_toContinuousMap, Circle.turnLift_apply, Set.Icc.coe_one,
    Set.Icc.coe_zero, mul_one, mul_zero, sub_zero] at hdisplacement
  exact_mod_cast hdisplacement.symm

/-- Definition 66.4 (3): The standard loop
`s ↦ (Real.cos (2 * Real.pi * s), Real.sin (2 * Real.pi * s))` is counterclockwise. -/
theorem standardLoop_isCounterclockwise :
    IsCounterclockwise standardLoop := by
  -- Use the origin, whose winding number was computed by the explicit lift.
  rw [isCounterclockwise_iff]
  refine ⟨0, zero_not_mem_range_standardLoop, ?_⟩
  constructor
  · -- An unbounded origin component would have winding number zero by Theorem 66.2.
    by_contra hbounded
    have hzero := windingNumber_eq_zero_of_component_unbounded standardLoop 0
      standardLoop_isSimple zero_not_mem_range_standardLoop hbounded
    rw [windingNumber_standardLoop_zero] at hzero
    norm_num at hzero
  · exact windingNumber_standardLoop_zero


end PlaneLoop
