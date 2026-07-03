import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_14_27 (from Items/Chap14) -/
open scoped MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory

noncomputable section

universe u

variable {E : Type u} [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]

/-- The kernel sending `y` to the convolution `δ_y ∗ ν`. -/
def dirac_convolution_kernel (ν : Measure E) [SFinite ν] : Kernel E E :=
  (Kernel.id ×ₖ Kernel.const E ν).map (fun p : E × E ↦ p.1 + p.2)

/-- The value of `dirac_convolution_kernel ν` at `y` is `δ_y ∗ ν`. -/
@[simp]
theorem dirac_convolution_kernel_apply (ν : Measure E) [SFinite ν] (y : E) :
    dirac_convolution_kernel ν y = Measure.dirac y ∗ ν := by
  rw [dirac_convolution_kernel, Kernel.map_apply _ measurable_add, Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map measurable_add measurable_prodMk_left]
  simpa [Function.comp_def] using (Measure.dirac_conv y ν).symm

/-- Lemma 14.27: composing the constant kernel with value `μ` and the translation kernel
`y ↦ δ_y ∗ ν` yields the constant kernel with value `μ ∗ ν`. In the source this is applied on
`ℝ^d`; the Lean statement keeps the same mathematics in the canonical additive-kernel form. -/
theorem dirac_convolution_kernel_comp_const_eq_const_conv
    (μ ν : Measure E)
    [SFinite μ] [SFinite ν] :
    dirac_convolution_kernel ν ∘ₖ Kernel.const E μ = Kernel.const E (μ ∗ ν) := by
  rw [ProbabilityTheory.Kernel.comp_const]
  congr 1
  rw [dirac_convolution_kernel,
    ← Measure.map_comp μ (Kernel.id ×ₖ Kernel.const E ν) measurable_add,
    ← Measure.compProd_eq_comp_prod μ (Kernel.const E ν),
    Measure.compProd_const]
  rfl
