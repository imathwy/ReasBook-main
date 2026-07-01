import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A family in `L¹(μ)` satisfies the integrable-weight condition from Theorem 6.24 if there is
an integrable `μ`-a.e. nonnegative weight for which the source theorem's condition `(ii)` holds.
This is the source-facing weight criterion; the owner small-set abstraction remains
`MeasureTheory.UnifIntegrable`. -/
def HasIntegrableWeightControl (F : Set (Lp ℝ 1 μ)) : Prop :=
  ∃ weight : Ω → ℝ,
    0 ≤ᵐ[μ] weight ∧
      Integrable weight μ ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ s : Set Ω, MeasurableSet s → ∫ x in s, weight x ∂μ < δ →
            ∀ ⦃f : Lp ℝ 1 μ⦄, f ∈ F → ∫ x in s, |f x| ∂μ ≤ ε

/-- Theorem 6.24 bridge: the source's integrable-weight criterion is exactly the small-set part of
uniform integrability, namely `UnifIntegrable` for the subtype family `F`. -/
theorem hasIntegrableWeightControl_iff_unifIntegrable (F : Set (Lp ℝ 1 μ)) :
    HasIntegrableWeightControl F ↔ UnifIntegrable ((↑) : F → Ω → ℝ) 1 μ := sorry

-- Proof sketch: combine the canonical boundedness factor in the definition of
-- `UniformIntegrable` for `L¹` families with the integrable-weight criterion for the small-set
-- clause.
/-- Theorem 6.24: a family in `L¹(μ)` is uniformly integrable if and only if it is bounded in the
chapter sense of Definition 6.20 and satisfies condition `(ii)` of the source theorem. -/
theorem uniformIntegrable_iff_isBounded_and_exists_integrable_weight_control
    (F : Set (Lp ℝ 1 μ)) :
    UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ ↔
      Bornology.IsBounded F ∧ HasIntegrableWeightControl F := sorry

/-- On a finite measure space, condition `(ii)` in Theorem 6.24 is equivalent to the small-measure
formulation `(iii)` from the source text. -/
theorem exists_integrable_weight_control_iff_small_measure_integral_control
    (F : Set (Lp ℝ 1 μ)) [IsFiniteMeasure μ] :
    HasIntegrableWeightControl F ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : Set Ω, MeasurableSet s → μ s < ENNReal.ofReal δ →
          ∀ ⦃f : Lp ℝ 1 μ⦄, f ∈ F → ∫ x in s, |f x| ∂μ ≤ ε := sorry

/-- On a finite measure space, Theorem 6.24 can be read directly in terms of the canonical owner
predicate `UniformIntegrable`: boundedness in `L¹(μ)` plus the source small-measure control
criterion. -/
theorem uniformIntegrable_iff_isBounded_and_small_measure_integral_control
    (F : Set (Lp ℝ 1 μ)) [IsFiniteMeasure μ] :
    UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ ↔
      Bornology.IsBounded F ∧
        (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ s : Set Ω, MeasurableSet s → μ s < ENNReal.ofReal δ →
            ∀ ⦃f : Lp ℝ 1 μ⦄, f ∈ F → ∫ x in s, |f x| ∂μ ≤ ε) := by
  rw [uniformIntegrable_iff_isBounded_and_exists_integrable_weight_control]
  constructor
  · rintro ⟨h_bounded, h_weight⟩
    exact ⟨h_bounded,
      (exists_integrable_weight_control_iff_small_measure_integral_control F).mp h_weight⟩
  · rintro ⟨h_bounded, h_small⟩
    exact ⟨h_bounded,
      (exists_integrable_weight_control_iff_small_measure_integral_control F).mpr h_small⟩
