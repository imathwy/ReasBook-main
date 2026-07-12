import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Exercise 13 (1): On `[0, π / 2]`, one has the lower Jordan bound
`2 / π * x ≤ sin x`. -/
recall Real.mul_le_sin

/- Exercise 13 (2): The interval upper bound `sin x ≤ x` follows from the
stronger canonical inequality valid for every real `x ≥ 0`. -/
recall Real.sin_le
