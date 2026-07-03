import ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_11

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u v

variable {ι : Type u} [Preorder ι]
variable {Ω : Type v} {m0 : MeasurableSpace Ω}
variable {ℱ 𝒢 : Filtration ι m0} {μ : Measure Ω} [IsFiniteMeasure μ]
variable {X : ι → Ω → ℝ}

-- Proof sketch: combine the tower property
-- `μ[μ[X t | 𝒢 s] | ℱ s] = μ[X t | ℱ s]` with the martingale identity for `𝒢`, and use the
-- `ℱ s`-measurability of `X s` coming from the assumed adaptation to `ℱ`.
/-- Remark 9.29 (1): If `ℱ ≤ 𝒢`, a process is a martingale for the larger filtration `𝒢`, and it
is adapted to the smaller filtration `ℱ`, then it is already a martingale for `ℱ`. -/
theorem martingale_of_le_filtration (hℱ𝒢 : ℱ ≤ 𝒢) (hX : Martingale X 𝒢 μ)
    (hXad : Adapted ℱ X) :
    Martingale X ℱ μ := sorry

-- Proof sketch: apply the tower property to rewrite `μ[X t | ℱ s]` as
-- `μ[μ[X t | 𝒢 s] | ℱ s]`, use the `𝒢`-submartingale inequality inside the inner conditional
-- expectation, then collapse `μ[X s | ℱ s]` to `X s` using adaptation to `ℱ`.
/-- Remark 9.29 (2): If `ℱ ≤ 𝒢`, a process is a submartingale for the larger filtration `𝒢`, and
it is adapted to the smaller filtration `ℱ`, then it is already a submartingale for `ℱ`. -/
theorem submartingale_of_le_filtration (hℱ𝒢 : ℱ ≤ 𝒢) (hX : Submartingale X 𝒢 μ)
    (hXad : Adapted ℱ X) :
    Submartingale X ℱ μ := sorry

-- Proof sketch: rewrite `μ[X t | ℱ s]` by conditioning first with respect to `𝒢 s`, use the
-- `𝒢`-supermartingale inequality, and then identify `μ[X s | ℱ s]` with `X s` from the
-- adaptation hypothesis.
/-- Remark 9.29 (3): If `ℱ ≤ 𝒢`, a process is a supermartingale for the larger filtration `𝒢`,
and it is adapted to the smaller filtration `ℱ`, then it is already a supermartingale for `ℱ`. -/
theorem supermartingale_of_le_filtration (hℱ𝒢 : ℱ ≤ 𝒢) (hX : Supermartingale X 𝒢 μ)
    (hXad : Adapted ℱ X) :
    Supermartingale X ℱ μ := sorry

-- Proof sketch: the natural filtration of `X` is contained in `ℱ` by
-- `adapted_iff_natural_le`, using the strong measurability obtained from `hX.stronglyAdapted`;
-- then apply
-- `martingale_of_le_filtration`.
/-- A martingale is also a martingale with respect to its own natural filtration. -/
theorem martingale_natural_filtration (hX : Martingale X ℱ μ) :
    Martingale X
      (Filtration.natural X (fun i ↦ (hX.stronglyAdapted i).mono (ℱ.le i))) μ := by
  let hXm : ∀ i, StronglyMeasurable (X i) := fun i ↦ (hX.stronglyAdapted i).mono (ℱ.le i)
  let hXmeas : ∀ i, Measurable (X i) := fun i ↦ (hXm i).measurable
  have hgen : generatedFiltration X hXmeas ≤ ℱ :=
    (adapted_iff_generatedFiltration_le hXmeas).mp hX.stronglyAdapted.adapted
  have hnat : Filtration.natural X hXm ≤ ℱ := by
    simpa [generatedFiltration_eq_natural X hXm] using hgen
  refine martingale_of_le_filtration
    hnat hX (Filtration.stronglyAdapted_natural hXm).adapted

-- Proof sketch: use the containment of the natural filtration in `ℱ` coming from the
-- strong measurability of the submartingale via `adapted_iff_natural_le`, then apply
-- `submartingale_of_le_filtration`.
/-- A submartingale is also a submartingale with respect to its own natural filtration. -/
theorem submartingale_natural_filtration (hX : Submartingale X ℱ μ) :
    Submartingale X
      (Filtration.natural X (fun i ↦ (hX.stronglyAdapted i).mono (ℱ.le i))) μ := by
  let hXm : ∀ i, StronglyMeasurable (X i) := fun i ↦ (hX.stronglyAdapted i).mono (ℱ.le i)
  let hXmeas : ∀ i, Measurable (X i) := fun i ↦ (hXm i).measurable
  have hgen : generatedFiltration X hXmeas ≤ ℱ :=
    (adapted_iff_generatedFiltration_le hXmeas).mp hX.stronglyAdapted.adapted
  have hnat : Filtration.natural X hXm ≤ ℱ := by
    simpa [generatedFiltration_eq_natural X hXm] using hgen
  refine submartingale_of_le_filtration
    hnat hX (Filtration.stronglyAdapted_natural hXm).adapted

-- Proof sketch: the natural filtration is smaller than `ℱ` by `adapted_iff_natural_le`, and the
-- supermartingale statement then follows from `supermartingale_of_le_filtration`.
/-- A supermartingale is also a supermartingale with respect to its own natural filtration. -/
theorem supermartingale_natural_filtration (hX : Supermartingale X ℱ μ) :
    Supermartingale X
      (Filtration.natural X (fun i ↦ (hX.stronglyAdapted i).mono (ℱ.le i))) μ := by
  let hXm : ∀ i, StronglyMeasurable (X i) := fun i ↦ (hX.stronglyAdapted i).mono (ℱ.le i)
  let hXmeas : ∀ i, Measurable (X i) := fun i ↦ (hXm i).measurable
  have hgen : generatedFiltration X hXmeas ≤ ℱ :=
    (adapted_iff_generatedFiltration_le hXmeas).mp hX.stronglyAdapted.adapted
  have hnat : Filtration.natural X hXm ≤ ℱ := by
    simpa [generatedFiltration_eq_natural X hXm] using hgen
  refine supermartingale_of_le_filtration
    hnat hX (Filtration.stronglyAdapted_natural hXm).adapted
