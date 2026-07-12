import Mathlib

open scoped PowerSeries

/- Definition I.1-extra-3: the order of a formal power series is the canonical function
`PowerSeries.order : R⟦X⟧ → ℕ∞`. For a nonzero series it is the least index of a nonzero
coefficient, while the zero series has order `⊤`, so the inequality `ω(S) ≥ k` also makes
sense for `S = 0`. -/
recall PowerSeries.order
