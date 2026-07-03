import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_19 (from Items/Chap09) -/
open MeasureTheory

/- Definition 9.19: For a stopping time `τ` with respect to a filtration `ℱ`, the σ-algebra of
the `τ`-past is the canonical mathlib measurable space `IsStoppingTime.measurableSpace`
attached to a proof `hτ : IsStoppingTime ℱ τ`. -/
recall IsStoppingTime.measurableSpace

/- Membership in the stopping-time past σ-algebra is characterized by the textbook condition
`A ∩ {τ ≤ t} ∈ ℱ_t` for every time `t`. -/
recall IsStoppingTime.measurableSet
