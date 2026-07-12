import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap04.Definition_4_7
import ProbabilityTheory_Klenke_2020.Items.Chap14.Corollary_14_23

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u v

section

variable {Ω₁ : Type u} {Ω₂ : Type v}
variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/- Source-facing layer: Theorem 14.29 is about the canonical product measure from Corollary 14.23
attached to a finite measure `μ` and a finite transition kernel `κ`. The core/canonical
integration engine is the product-measure Tonelli/Fubini API from Theorem 14.16; a direct
`μ ⊗ₘ κ` formulation is only a stronger bridge/view when extra mathlib s-finiteness hypotheses are
available. -/
variable (μ : Measure Ω₁) [IsFiniteMeasure μ] (κ : Kernel Ω₁ Ω₂)

-- Proof sketch: use Corollary 14.23 to identify `ν` with the source-facing product measure of `μ`
-- and `κ`, then apply the right-iterated Tonelli theorem from Theorem 14.16.
/-- Theorem 14.29: for the source-facing product measure determined by `μ` and `κ`, the canonical
right-iterated `toENNReal` Tonelli identity holds. -/
theorem tonelli_transition_kernel
    (hκ : IsFiniteTransitionKernel κ)
    {f : Ω₁ × Ω₂ → EReal} (hf : Measurable f) :
    ∫⁻ z, (f z).toENNReal ∂finiteTransitionKernelProductMeasure μ κ hκ =
      ∫⁻ ω₁, ∫⁻ ω₂, (f (ω₁, ω₂)).toENNReal ∂κ ω₁ ∂μ := sorry

-- Proof sketch: after identifying `ν` with the Chapter 14 product measure from Corollary 14.23,
-- apply the right-iterated `EReal` Fubini theorem from Theorem 14.16.
/-- Theorem 14.29: for an `erealIntegrable` function on the product measure from Corollary 14.23,
the chapter `EReal` integral is the iterated difference of the positive-part and negative-part
lower integrals. -/
theorem fubini_transition_kernel
    (hκ : IsFiniteTransitionKernel κ)
    {f : Ω₁ × Ω₂ → EReal}
    (hf : erealIntegrable f (finiteTransitionKernelProductMeasure μ κ hκ)) :
    erealIntegral f (finiteTransitionKernelProductMeasure μ κ hκ) hf.defined =
      (((∫⁻ ω₁, ∫⁻ ω₂, (f (ω₁, ω₂)).toENNReal ∂κ ω₁ ∂μ) : EReal) -
        ((∫⁻ ω₁, ∫⁻ ω₂, (-f (ω₁, ω₂)).toENNReal ∂κ ω₁ ∂μ) : EReal)) := sorry

end
