import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 1.2.7: the usual real-valued absolute value on `ℚ` is mathlib's canonical owner
`Rat.AbsoluteValue.real : AbsoluteValue ℚ ℝ`; its evaluation formula is
`Rat.AbsoluteValue.real_eq_abs`, and the absolute-value predicate is the bundled fact
`Rat.AbsoluteValue.real.isAbsoluteValue`. -/
recall Rat.AbsoluteValue.real : AbsoluteValue ℚ ℝ

#check Rat.AbsoluteValue.real_eq_abs

#check (Rat.AbsoluteValue.real.isAbsoluteValue : IsAbsoluteValue Rat.AbsoluteValue.real)
