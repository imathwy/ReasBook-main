module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

public section

/-- Exercise 24.2: A continuous real-valued function on the unit circle takes the
same value at some pair of antipodal points. -/
theorem existsAntipodalEqOfContinuous
    (f : C(Circle, ℝ)) :
    ∃ x, f x = f (-x) := by
  -- Compare the values at one antipodal pair to orient the IVT endpoints.
  let a : Circle := 1
  have hAntipodal : Continuous (fun x : Circle ↦ f (-x)) :=
    f.continuous.comp continuous_neg
  rcases le_total (f a) (f (-a)) with hForward | hBackward
  · -- Along the endpoints `a, -a`, the two continuous functions reverse order.
    refine intermediate_value_univ₂ (a := a) (b := -a) f.continuous hAntipodal hForward ?_
    simpa using hForward
  · -- If the initial order is reversed, interchange the two endpoints.
    refine intermediate_value_univ₂ (a := -a) (b := a) f.continuous hAntipodal ?_ hBackward
    simpa using hBackward
