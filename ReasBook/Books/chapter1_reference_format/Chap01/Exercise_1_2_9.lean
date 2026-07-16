import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Exercise 1.2.9 (1): the relation `<` on `ℝ` is a strict total order relation. -/
#check (inferInstance : IsStrictTotalOrder ℝ (· < ·))

/- Exercise 1.2.9 (2): the formula `q ↦ |(q : ℝ)|` is mathlib's canonical real-valued absolute
value on `ℚ`, namely `Rat.AbsoluteValue.real`; its evaluation formula is
`Rat.AbsoluteValue.real_eq_abs`, and the bundled absolute-value predicate is
`Rat.AbsoluteValue.real.isAbsoluteValue`. -/
recall Rat.AbsoluteValue.real : AbsoluteValue ℚ ℝ

#check Rat.AbsoluteValue.real_eq_abs

#check (Rat.AbsoluteValue.real.isAbsoluteValue : IsAbsoluteValue Rat.AbsoluteValue.real)
