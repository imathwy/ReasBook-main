import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/- Lemma 9.21: if `σ` and `τ` are stopping times with `σ ≤ τ`, then the stopping-time
σ-algebra `𝓕_σ` is contained in `𝓕_τ`; in mathlib this is the canonical monotonicity theorem for
`IsStoppingTime.measurableSpace`. -/
recall IsStoppingTime.measurableSpace_mono
