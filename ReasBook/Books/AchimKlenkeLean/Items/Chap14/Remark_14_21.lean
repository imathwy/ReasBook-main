import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

variable {Ω₁ : Type*} {Ω₂ : Type*}
variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/- Remark 14.21: the textbook display notation
`∫ κ(ω₁, dω₂) f(ω₁, ω₂)` is just the standard kernel integral
`∫ ω₂, f (ω₁, ω₂) ∂κ ω₁`. This is the source-facing term underlying the canonical kernel-product
APIs such as `ProbabilityTheory.Kernel.lintegral_id_prod`; the remark itself is only typographical,
moving the fiber measure `κ ω₁` closer to the corresponding integral sign in iterated integrals. -/
#check fun (κ : Kernel Ω₁ Ω₂) (f : Ω₁ × Ω₂ → ℝ) ω₁ ↦ ∫ ω₂, f (ω₁, ω₂) ∂κ ω₁
