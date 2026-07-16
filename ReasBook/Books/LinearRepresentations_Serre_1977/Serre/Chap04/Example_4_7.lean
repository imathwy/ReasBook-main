import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import LinearRepresentations_Serre_1977.Serre.Chap04.Theorem_4_5

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section

-- Source/core/bridge triage:
-- `source-facing`: the singleton-mass and averaging formulas from Example 4-7;
-- `core/canonical`: `Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)`;
-- `bridge/view`: the finite-group identity with `Measure.count` and its source-facing companions.

universe u v

section FiniteGroup

variable {G : Type u} [Group G] [Finite G] [TopologicalSpace G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]

local instance instFintypeExample_4_7FiniteGroup : Fintype G := Fintype.ofFinite G

attribute [local instance] Finite.compactSpace

/-- On a finite group, the canonical normalized Haar measure is the inverse-cardinality multiple
of the counting measure. -/
theorem normalizedHaarMeasure_eq_inv_card_smul_count :
    normalizedHaarMeasure = (Nat.card G : ℝ≥0∞)⁻¹ • (Measure.count : Measure G) := by
  have hcard_ne_zero : (Nat.card G : ℝ≥0∞) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  let ν : Measure G := (Nat.card G : ℝ≥0∞)⁻¹ • (Measure.count : Measure G)
  have hν_univ : ν Set.univ = 1 := by
    rw [show ν = (Nat.card G : ℝ≥0∞)⁻¹ • (Measure.count : Measure G) by rfl]
    rw [Measure.smul_apply, Measure.count_univ]
    simpa using ENNReal.inv_mul_cancel hcard_ne_zero (by simp)
  haveI : IsProbabilityMeasure ν := ⟨hν_univ⟩
  have h := eq_normalizedHaarMeasure_of_isProbabilityMeasure_of_isMulRightInvariant ν
  simpa [normalizedHaarMeasure, ν] using h.symm

/-- Example 4-7 (1): if `G` is a finite group, then the normalized Haar measure of each singleton
is `(Nat.card G : ℝ≥0∞)⁻¹`. -/
theorem normalizedHaarMeasure_apply_singleton [MeasurableSingletonClass G] (t : G) :
    μG {t} = (Nat.card G : ℝ≥0∞)⁻¹ := by
  change normalizedHaarMeasure {t} = (Nat.card G : ℝ≥0∞)⁻¹
  rw [normalizedHaarMeasure_eq_inv_card_smul_count]
  simp

/-- Example 4-7 (2): if `G` is a finite group, then integrating a function against the normalized
Haar measure is averaging over all elements of `G`. -/
theorem normalizedHaarMeasure_integral_eq_average {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSingletonClass G]
    (f : G → E) :
    (∫ t, f t ∂μG) =
      (Nat.card G : ℝ)⁻¹ • ∑ t, f t := by
  change (∫ t, f t ∂normalizedHaarMeasure) = (Nat.card G : ℝ)⁻¹ • ∑ t, f t
  rw [normalizedHaarMeasure_eq_inv_card_smul_count, integral_smul_measure, integral_count]
  simp

end FiniteGroup
