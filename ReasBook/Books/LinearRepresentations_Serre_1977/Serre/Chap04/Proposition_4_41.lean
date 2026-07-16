import LinearRepresentations_Serre_1977.Serre.Chap04.Theorem_4_5
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

-- Semantic recall note: `lean_leansearch` and local mathlib search point to
-- `Measure.prod.instIsHaarMeasure` and `MeasureTheory.integral_prod` as the canonical
-- product-measure and Fubini surfaces for this item.

variable {G₁ : Type} [Group G₁] [TopologicalSpace G₁] [CompactSpace G₁]
  [MeasurableSpace G₁] [BorelSpace G₁] [IsTopologicalGroup G₁]
variable {G₂ : Type} [Group G₂] [TopologicalSpace G₂] [CompactSpace G₂]
  [MeasurableSpace G₂] [BorelSpace G₂] [IsTopologicalGroup G₂]

/-- Proposition 4-41 (1): the normalized Haar measure `μG` on the product compact group
`G₁ × G₂` is the product of the normalized Haar measures `μG` on `G₁` and `G₂`. -/
theorem normalizedHaarMeasure_prod [BorelSpace (G₁ × G₂)] :
    (μG : Measure (G₁ × G₂)) = (μG : Measure G₁).prod (μG : Measure G₂) := by
  let μprod : Measure (G₁ × G₂) := (μG : Measure G₁).prod (μG : Measure G₂)
  have h : (μG : Measure (G₁ × G₂)) = μprod :=
    Measure.isHaarMeasure_eq_of_isProbabilityMeasure (μG : Measure (G₁ × G₂)) μprod
  simpa [μprod] using h

/-- Fubini's theorem for the product of the normalized Haar measures `μG` on `G₁` and `G₂`. This
is the canonical product-measure form behind Proposition 4-41 (2). -/
theorem integral_prod_normalizedHaarMeasure {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : G₁ × G₂ → E)
    (hf : Integrable f ((μG : Measure G₁).prod (μG : Measure G₂))) :
    (∫ z, f z ∂((μG : Measure G₁).prod (μG : Measure G₂))) =
      ∫ s₁, ∫ s₂, f (s₁, s₂) ∂(μG : Measure G₂) ∂(μG : Measure G₁) := by
  simpa using integral_prod f hf

/-- Proposition 4-41 (2): for every continuous `f : G₁ × G₂ → ℂ`, integrating `f` against the
normalized Haar measure `μG` on `G₁ × G₂` is the iterated integral against the normalized Haar
measures `μG` on `G₁` and `G₂`. -/
theorem integral_normalizedHaarMeasure_prod
    [BorelSpace (G₁ × G₂)]
    (f : G₁ × G₂ → ℂ) (hf : Continuous f) :
    (∫ z, f z ∂(μG : Measure (G₁ × G₂))) =
      ∫ s₁, ∫ s₂, f (s₁, s₂) ∂(μG : Measure G₂) ∂(μG : Measure G₁) := by
  have hcompact : HasCompactSupport f := by
    rw [hasCompactSupport_def]
    exact IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport f) <|
      by intro z hz; simp
  have h_integrable : Integrable f ((μG : Measure G₁).prod (μG : Measure G₂)) :=
    hf.integrable_of_hasCompactSupport hcompact
  calc
    (∫ z, f z ∂(μG : Measure (G₁ × G₂))) =
        ∫ z, f z ∂((μG : Measure G₁).prod (μG : Measure G₂)) := by
          rw [normalizedHaarMeasure_prod]
    _ = ∫ s₁, ∫ s₂, f (s₁, s₂) ∂(μG : Measure G₂) ∂(μG : Measure G₁) :=
      integral_prod_normalizedHaarMeasure f h_integrable
