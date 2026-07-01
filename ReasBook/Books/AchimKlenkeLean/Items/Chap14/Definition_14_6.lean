import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open MeasureTheory

variable {I : Type u} {E : Type v}

/- Definition 14.6: for a measurable space `(E, ℰ)` and the product measurable space on `E^I`,
the canonical process is the family of coordinate maps `X_t (ω) = ω t`, namely
`Function.eval : I → (I → E) → E`. -/
#check (Function.eval : I → (I → E) → E)

/- Each coordinate of the canonical process is measurable for the product measurable space on
`I → E`; this is exactly `measurable_pi_apply`. -/
section

variable [MeasurableSpace E]

#check (measurable_pi_apply : ∀ t : I, Measurable (Function.eval t : (I → E) → E))

end
