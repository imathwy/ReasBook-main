

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_12_18 (from Items/Chap12) -/
open MeasureTheory
open scoped symmDiff

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {μ : Measure Ω} [IsFiniteMeasure μ]

/-
Corollary 12.18 is a `source-facing` event-level statement. Its owner abstractions are the Chapter
12 exchangeable `σ`-algebra `exchangeableSigmaAlgebra (Function.swap X)` and the Chapter 2 tail
`σ`-algebra `tailRandomVariableMeasurableSpace X`. The null-symmetric-difference reformulation is
kept only as a `bridge/view` companion via the canonical mathlib theorem
`measure_symmDiff_eq_zero_iff`.
-/

-- Proof sketch: apply Theorem 12.17 to the indicators of finite-cylinder approximations of `A` to
-- obtain a `tailRandomVariableMeasurableSpace X`-measurable version of `𝟙_A`; then realize that version
-- as the indicator of a tail event `B`, which gives `A =ᵐ[μ] B`.
/-- Corollary 12.18: for an exchangeable sequence, every event in the exchangeable
`σ`-algebra over a finite measure space agrees up to a null set with an event in the tail
`σ`-algebra. -/
theorem exists_tail_measurableSet_ae_eq_of_mem_exchangeableSigmaAlgebra
    {X : ℕ → Ω → E} (hX : IsExchangeable X μ) {A : Set Ω}
    (hA : MeasurableSet[exchangeableSigmaAlgebra (Function.swap X)] A) :
    ∃ B : Set Ω, MeasurableSet[tailRandomVariableMeasurableSpace X] B ∧ A =ᵐ[μ] B := sorry

-- Proof sketch: this is the measure-theoretic reformulation of
-- `exists_tail_measurableSet_ae_eq_of_mem_exchangeableSigmaAlgebra` via
-- `measure_symmDiff_eq_zero_iff`.
/-- Bridge companion to Corollary 12.18: the canonical almost-everywhere event equality can be
rewritten as vanishing symmetric-difference measure. -/
theorem exists_tail_measurableSet_symmDiff_null_of_mem_exchangeableSigmaAlgebra
    {X : ℕ → Ω → E} (hX : IsExchangeable X μ) {A : Set Ω}
    (hA : MeasurableSet[exchangeableSigmaAlgebra (Function.swap X)] A) :
    ∃ B : Set Ω, MeasurableSet[tailRandomVariableMeasurableSpace X] B ∧ μ (A ∆ B) = 0 := by
  rcases exists_tail_measurableSet_ae_eq_of_mem_exchangeableSigmaAlgebra hX hA with
    ⟨B, hB, hAB⟩
  exact ⟨B, hB, measure_symmDiff_eq_zero_iff.mpr hAB⟩
