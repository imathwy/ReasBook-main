import Mathlib
import AchimKlenkeLean.Items.Chap14.Theorem_14_22

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u v

section

variable {Ω₁ : Type u} {Ω₂ : Type v}
variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/- Source-facing layer: under the rowwise-finite hypothesis `IsFiniteTransitionKernel κ`, the
canonical chapter-level owner is the product kernel from Theorem 14.22 specialized to the
constant first-step kernel `Kernel.const Unit μ` and `Kernel.prodMkLeft Unit κ`. The stronger
mathlib owner `μ ⊗ₘ κ` requires `IsSFiniteKernel κ`, so it is used only for the Markov corollary
below, not for this theorem. -/
-- Proof sketch: specialize Theorem 14.22 to `Kernel.const Unit μ` and `Kernel.prodMkLeft Unit κ`;
-- this gives the witness measure on `Ω₁ × Ω₂`, its σ-finiteness, and the rectangle formula.
-- Uniqueness is then the source-facing rectangle uniqueness statement for that specialized
-- product-kernel construction.
/-- Corollary 14.23: a finite measure `μ` and a finite transition kernel `κ` determine a unique
σ-finite measure on the product space whose value on measurable rectangles is
`∫⁻ ω₁ in A₁, κ ω₁ A₂ ∂μ`. -/
theorem existsUnique_sigmaFinite_product_measure_of_isFiniteTransitionKernel
    (μ : Measure Ω₁) [IsFiniteMeasure μ] (κ : Kernel Ω₁ Ω₂) (hκ : IsFiniteTransitionKernel κ) :
    ∃! ν : Measure (Ω₁ × Ω₂),
      SigmaFinite ν ∧
        ∀ A₁ : Set Ω₁, ∀ A₂ : Set Ω₂,
          MeasurableSet A₁ → MeasurableSet A₂ →
            ν (A₁ ×ˢ A₂) = ∫⁻ ω₁ in A₁, κ ω₁ A₂ ∂μ := by
  let κμ : Kernel Unit Ω₁ := Kernel.const Unit μ
  let κ' : Kernel (Unit × Ω₁) Ω₂ := Kernel.prodMkLeft Unit κ
  let ν : Measure (Ω₁ × Ω₂) := transitionKernelProduct κμ κ' ()
  refine ⟨ν, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · sorry
    · intro A₁ A₂ hA₁ hA₂
      sorry
  · intro ν hν
    sorry

/-- The canonical product measure from Corollary 14.23 attached to a finite measure `μ` and a
finite transition kernel `κ`. -/
noncomputable def finiteTransitionKernelProductMeasure
    (μ : Measure Ω₁) [IsFiniteMeasure μ] (κ : Kernel Ω₁ Ω₂)
    (hκ : IsFiniteTransitionKernel κ) : Measure (Ω₁ × Ω₂) :=
  Classical.choose <|
    existsUnique_sigmaFinite_product_measure_of_isFiniteTransitionKernel μ κ hκ

private theorem finiteTransitionKernelProductMeasure_spec
    (μ : Measure Ω₁) [IsFiniteMeasure μ] (κ : Kernel Ω₁ Ω₂)
    (hκ : IsFiniteTransitionKernel κ) :
    SigmaFinite (finiteTransitionKernelProductMeasure μ κ hκ) ∧
      ∀ A₁ : Set Ω₁, ∀ A₂ : Set Ω₂,
        MeasurableSet A₁ → MeasurableSet A₂ →
          finiteTransitionKernelProductMeasure μ κ hκ (A₁ ×ˢ A₂) =
            ∫⁻ ω₁ in A₁, κ ω₁ A₂ ∂μ :=
  (Classical.choose_spec <|
    existsUnique_sigmaFinite_product_measure_of_isFiniteTransitionKernel μ κ hκ).1

/-- The canonical product measure from Corollary 14.23 is sigma-finite. -/
theorem sigmaFinite_finiteTransitionKernelProductMeasure
    (μ : Measure Ω₁) [IsFiniteMeasure μ] (κ : Kernel Ω₁ Ω₂)
    (hκ : IsFiniteTransitionKernel κ) :
    SigmaFinite (finiteTransitionKernelProductMeasure μ κ hκ) :=
  (finiteTransitionKernelProductMeasure_spec μ κ hκ).1

/-- On measurable rectangles, the canonical product measure from Corollary 14.23 satisfies the
textbook transition-kernel formula. -/
theorem finiteTransitionKernelProductMeasure_apply_prod
    (μ : Measure Ω₁) [IsFiniteMeasure μ] (κ : Kernel Ω₁ Ω₂)
    (hκ : IsFiniteTransitionKernel κ)
    (A₁ : Set Ω₁) (A₂ : Set Ω₂)
    (hA₁ : MeasurableSet A₁) (hA₂ : MeasurableSet A₂) :
    finiteTransitionKernelProductMeasure μ κ hκ (A₁ ×ˢ A₂) =
      ∫⁻ ω₁ in A₁, κ ω₁ A₂ ∂μ :=
  (finiteTransitionKernelProductMeasure_spec μ κ hκ).2 A₁ A₂ hA₁ hA₂

-- Proof sketch: use the canonical mathlib instance stating that the composition-product of a
-- probability measure with a Markov kernel is again a probability measure.
/- The composition-product of a probability measure with a stochastic kernel is already the
canonical mathlib owner instance on `μ ⊗ₘ κ`, so this corollary is recorded by direct reuse
rather than a parallel local wrapper theorem. -/
example
    (μ : Measure Ω₁) [IsProbabilityMeasure μ] (κ : Kernel Ω₁ Ω₂) [IsMarkovKernel κ] :
    IsProbabilityMeasure (μ ⊗ₘ κ) :=
  inferInstance

end
