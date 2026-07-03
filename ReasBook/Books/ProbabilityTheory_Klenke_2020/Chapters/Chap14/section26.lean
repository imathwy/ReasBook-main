import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_14_26 (from Items/Chap14) -/
open ProbabilityTheory

universe u v w

section KernelComposition

variable {Ω₀ : Type u} {Ω₁ : Type v} {Ω₂ : Type w}
variable [MeasurableSpace Ω₀] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/- Theorem 14.26: the textbook composition `(κ₁ · κ₂)` is the second marginal of the
composition-product kernel. This is exactly the owner theorem
`ProbabilityTheory.Kernel.comp_eq_snd_compProd`. -/
recall Kernel.comp_eq_snd_compProd

/- The composition of two sub-Markov kernels is again a sub-Markov kernel. This is the owner
theorem `ProbabilityTheory.IsSubMarkovKernel.comp`. -/
recall IsSubMarkovKernel.comp

end KernelComposition
