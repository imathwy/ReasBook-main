import Mathlib
import ProbabilityTheory_Klenke_2020.Chap08.Definition_8_25

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u v w

section FiniteTransitionKernelProduct

variable {Ω₀ : Type u} {Ω₁ : Type v} {Ω₂ : Type w}
variable [MeasurableSpace Ω₀] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/- Source-facing layer: Theorem 14.22 builds the rowwise-finite product kernel directly from the
iterated-integral formula. The core/canonical owner for the s-finite setting is
`ProbabilityTheory.Kernel.compProd`; we keep that as a bridge/view only, since outside
`IsSFiniteKernel` mathlib defines `κ₁ ⊗ₖ κ₂` to be `0`. -/

/-- The measurable-set content used to build the product measure
`transitionKernelProduct κ₁ κ₂ ω₀` on `Ω₁ × Ω₂` at a fixed base point `ω₀`. -/
private noncomputable def productContent
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂) (ω₀ : Ω₀)
    (s : Set (Ω₁ × Ω₂)) (_hs : MeasurableSet s) : ℝ≥0∞ :=
  ∫⁻ ω₁, κ₂ (ω₀, ω₁) (Prod.mk ω₁ ⁻¹' s) ∂κ₁ ω₀

-- Proof sketch: for the empty measurable set, every section `Prod.mk ω₁ ⁻¹' ∅` is empty, so the
-- inner kernel values vanish and the outer `lintegral` is zero.
/-- The content defining the product transition measure sends the empty set to `0`. -/
private theorem productContent_empty
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂) (ω₀ : Ω₀) :
    productContent κ₁ κ₂ ω₀ ∅ MeasurableSet.empty = 0 := sorry

-- Proof sketch: apply monotone convergence to the disjoint measurable sections
-- `Prod.mk ω₁ ⁻¹' f i`, use countable additivity of each measure `κ₂ (ω₀, ω₁)`, and exchange the
-- resulting sum with the outer `lintegral`.
/-- The content defining the product transition measure is countably additive on pairwise disjoint
measurable unions. -/
private theorem productContent_iUnion
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂) (ω₀ : Ω₀)
    ⦃f : ℕ → Set (Ω₁ × Ω₂)⦄ (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise fun i j ↦ Disjoint (f i) (f j)) :
    productContent κ₁ κ₂ ω₀ (⋃ i, f i) (MeasurableSet.iUnion hf) =
      ∑' i, productContent κ₁ κ₂ ω₀ (f i) (hf i) := sorry

/-- The measure on `Ω₁ × Ω₂` obtained by integrating the fibers of `κ₂` against the row measure
`κ₁ ω₀`. -/
private noncomputable def productMeasure
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂) (ω₀ : Ω₀) : Measure (Ω₁ × Ω₂) :=
  Measure.ofMeasurable
    (productContent κ₁ κ₂ ω₀)
    (productContent_empty κ₁ κ₂ ω₀)
    (productContent_iUnion κ₁ κ₂ ω₀)

-- Proof sketch: unfold `productMeasure` and apply
-- `Measure.ofMeasurable_apply` to recover the defining iterated integral on measurable sets.
/-- On measurable subsets of `Ω₁ × Ω₂`, the product transition measure is given by the textbook
iterated integral formula. -/
private theorem productMeasure_apply
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂) (ω₀ : Ω₀)
    {s : Set (Ω₁ × Ω₂)} (hs : MeasurableSet s) :
    productMeasure κ₁ κ₂ ω₀ s =
      ∫⁻ ω₁, κ₂ (ω₀, ω₁) (Prod.mk ω₁ ⁻¹' s) ∂κ₁ ω₀ := sorry

-- Proof sketch: use `Measure.measurable_of_measurable_coe`; for each measurable `s`, Lemma 14.20
-- gives measurability of `ω₀ ↦ ∫⁻ ω₁, κ₂ (ω₀, ω₁) (Prod.mk ω₁ ⁻¹' s) ∂κ₁ ω₀`.
/-- The family of product measures depends measurably on the base point `ω₀`. -/
private theorem measurable_productMeasure
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂) :
    Measurable (productMeasure κ₁ κ₂) := sorry

/-- The source-facing product of a kernel `κ₁ : Ω₀ → Ω₁` and a kernel
`κ₂ : Ω₀ × Ω₁ → Ω₂`, defined rowwise by the iterated integral from Theorem 14.22. -/
noncomputable def transitionKernelProduct
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂) : Kernel Ω₀ (Ω₁ × Ω₂) :=
  ⟨productMeasure κ₁ κ₂, measurable_productMeasure κ₁ κ₂⟩

-- Proof sketch: this is the corresponding measurable-set formula for the kernel obtained by
-- packaging `productMeasure` into a `Kernel`.
/-- The product transition kernel evaluates on measurable sets by the same iterated integral
formula as its underlying row measures. -/
theorem transitionKernelProduct_apply
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂) (ω₀ : Ω₀)
    {s : Set (Ω₁ × Ω₂)} (hs : MeasurableSet s) :
    transitionKernelProduct κ₁ κ₂ ω₀ s =
      ∫⁻ ω₁, κ₂ (ω₀, ω₁) (Prod.mk ω₁ ⁻¹' s) ∂κ₁ ω₀ :=
  productMeasure_apply κ₁ κ₂ ω₀ hs

-- Proof sketch: `Kernel.prodMkLeft Ω₀ κ` has fiber `(ω₀, ω₁) ↦ κ ω₁`, so rowwise finiteness is
-- inherited immediately from the corresponding fiber of `κ`.
/-- Viewing a kernel `κ : Ω₁ → Ω₂` as a kernel on `Ω₀ × Ω₁` independent of `Ω₀` preserves rowwise
finiteness. -/
private theorem isFiniteTransitionKernel_prodMkLeft
    (κ : Kernel Ω₁ Ω₂) (hκ : IsFiniteTransitionKernel κ) :
    IsFiniteTransitionKernel (Kernel.prodMkLeft Ω₀ κ) := by
  intro ω
  simpa [Kernel.prodMkLeft_apply] using hκ ω.2

-- Proof sketch: compare both kernels on measurable sets; the source-facing definition and
-- mathlib's `κ₁ ⊗ₖ κ₂` satisfy the same rectangle-section integral formula, so extensionality gives
-- equality.
/-- Under the stronger s-finiteness assumptions from mathlib, the source-facing product kernel
agrees with the canonical composition-product `κ₁ ⊗ₖ κ₂`. -/
theorem transitionKernelProduct_eq_compProd
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂)
    [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    transitionKernelProduct κ₁ κ₂ = κ₁ ⊗ₖ κ₂ := by
  ext ω₀ s hs
  rw [transitionKernelProduct_apply κ₁ κ₂ ω₀ hs, Kernel.compProd_apply hs]

-- Proof sketch: for each `ω₀`, use the finite-fiber assumption on `κ₂` to cover `Ω₁ × Ω₂` by the
-- sets `A_{ω₀,n} ×ˢ univ` from the textbook proof, each having finite product-kernel mass; then
-- package the rowwise σ-finiteness into `IsSigmaFiniteTransitionKernel`.
/-- Theorem 14.22: if `κ₁ : Ω₀ → Ω₁` and `κ₂ : Ω₀ × Ω₁ → Ω₂` are finite transition kernels, then
their product kernel is a rowwise σ-finite transition kernel from `Ω₀` to `Ω₁ × Ω₂`. -/
theorem transitionKernelProduct_isSigmaFiniteTransitionKernel
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂)
    (hκ₁ : IsFiniteTransitionKernel κ₁) (hκ₂ : IsFiniteTransitionKernel κ₂) :
    IsSigmaFiniteTransitionKernel (transitionKernelProduct κ₁ κ₂) := sorry

-- Proof sketch: evaluate the product kernel on `univ`; the inner total masses are at most `1`
-- almost everywhere, so the iterated integral is bounded by the total mass of `κ₁`, which is also
-- at most `1`.
/-- Sub-Markov kernels are stable under the product construction of Theorem 14.22. -/
theorem transitionKernelProduct_isSubMarkovKernel
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂)
    (hκ₁ : IsSubMarkovKernel κ₁) (hκ₂ : IsSubMarkovKernel κ₂) :
    IsSubMarkovKernel (transitionKernelProduct κ₁ κ₂) := by
  letI : IsFiniteKernel κ₁ := ⟨⟨1, ENNReal.one_lt_top, hκ₁⟩⟩
  letI : IsFiniteKernel κ₂ := ⟨⟨1, ENNReal.one_lt_top, hκ₂⟩⟩
  have hκ₂_bound : κ₂.bound ≤ 1 := by
    refine iSup_le fun ω ↦ ?_
    simpa [Kernel.bound] using hκ₂ ω
  intro ω₀
  calc
    transitionKernelProduct κ₁ κ₂ ω₀ Set.univ = (κ₁ ⊗ₖ κ₂) ω₀ Set.univ := by
      rw [transitionKernelProduct_eq_compProd κ₁ κ₂]
    _ ≤ κ₁ ω₀ Set.univ * κ₂.bound := Kernel.compProd_apply_univ_le κ₁ κ₂ ω₀
    _ ≤ κ₁ ω₀ Set.univ * 1 := mul_le_mul_right hκ₂_bound _
    _ = κ₁ ω₀ Set.univ := by simp
    _ ≤ 1 := hκ₁ ω₀

-- Proof sketch: evaluate the product kernel on `univ`; now both total masses are exactly `1`, so
-- the iterated integral equals `1` for every base point.
/-- Markov kernels are stable under the product construction of Theorem 14.22. -/
theorem transitionKernelProduct_isMarkovKernel
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂)
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] :
    IsMarkovKernel (transitionKernelProduct κ₁ κ₂) := by
  simpa [transitionKernelProduct_eq_compProd κ₁ κ₂] using
    (inferInstance : IsMarkovKernel (κ₁ ⊗ₖ κ₂))

-- Proof sketch: specialize `transitionKernelProduct_apply` to `Kernel.prodMkLeft Ω₀ κ₂`, then use
-- `Kernel.sectR_prodMkLeft` or the defining formula of `prodMkLeft` to remove the dummy `Ω₀`
-- coordinate from the inner kernel.
/-- If the second factor is a kernel `κ₂ : Ω₁ → Ω₂`, viewing it as
`Kernel.prodMkLeft Ω₀ κ₂ : Kernel (Ω₀ × Ω₁) Ω₂` recovers the textbook supplementary definition of
the product. -/
theorem transitionKernelProduct_prodMkLeft_apply
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel Ω₁ Ω₂) (ω₀ : Ω₀)
    {s : Set (Ω₁ × Ω₂)} (hs : MeasurableSet s) :
    transitionKernelProduct κ₁ (Kernel.prodMkLeft Ω₀ κ₂) ω₀ s =
      ∫⁻ ω₁, κ₂ ω₁ (Prod.mk ω₁ ⁻¹' s) ∂κ₁ ω₀ := by
  simpa [Kernel.prodMkLeft_apply'] using
    transitionKernelProduct_apply κ₁ (Kernel.prodMkLeft Ω₀ κ₂) ω₀ hs

end FiniteTransitionKernelProduct
