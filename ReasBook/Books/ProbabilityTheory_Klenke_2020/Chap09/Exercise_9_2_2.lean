import Mathlib.Probability.Martingale.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Exercise 9.2.2: a predictable discrete-time martingale is almost surely constant in time, so
for every `n : ℕ` one has `X n = X 0` almost surely. This is exactly the canonical mathlib result
`MeasureTheory.Martingale.eq_zero_of_predictable'`. -/
recall MeasureTheory.Martingale.eq_zero_of_predictable'
