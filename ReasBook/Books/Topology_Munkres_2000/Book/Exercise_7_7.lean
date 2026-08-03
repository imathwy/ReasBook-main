module

public import Mathlib.Data.PNat.Basic
public import Mathlib.SetTheory.Cardinal.Continuum

public section

open scoped Cardinal

/-- Helper for Exercise 7.7: positive-integer-valued sequences have cardinality `𝔠`. -/
lemma positiveSequencesCardinality : Cardinal.mk (ℕ+ → ℕ+) = 𝔠 := by
  -- Rewrite the function space as cardinal exponentiation and identify both factors with `ℵ₀`.
  rw [Cardinal.mk_arrow, Cardinal.mk_pnat]
  simp only [Cardinal.lift_id]
  exact Cardinal.aleph0_power_aleph0

/-- Helper for Exercise 7.7: binary sequences indexed by positive integers have
cardinality `𝔠`. -/
lemma binaryPositiveSequencesCardinality : Cardinal.mk (ℕ+ → Fin 2) = 𝔠 := by
  -- The two-element base raised to a countably infinite exponent is the continuum.
  have htwo : 2 ≤ (2 : ℕ) := Nat.le_refl 2
  rw [Cardinal.mk_arrow, Cardinal.mk_pnat, Cardinal.mk_fin]
  simp only [Cardinal.lift_id]
  exact Cardinal.nat_power_aleph0 htwo

/-- Helper for Exercise 7.7: the two sequence spaces have equal cardinality. -/
lemma positiveSequencesCardinalEqBinarySequences :
    Cardinal.mk (ℕ+ → ℕ+) = Cardinal.mk (ℕ+ → Fin 2) := by
  -- Compare both cardinalities through their common continuum normal form.
  calc
    Cardinal.mk (ℕ+ → ℕ+) = 𝔠 := positiveSequencesCardinality
    _ = Cardinal.mk (ℕ+ → Fin 2) := binaryPositiveSequencesCardinality.symm

/-- Exercise 7.7: The positive-integer-valued sequences and binary sequences indexed
by the positive integers have the same cardinality. -/
theorem positiveSequencesEquivBinarySequences :
    Nonempty ((ℕ+ → ℕ+) ≃ (ℕ+ → Fin 2)) := by
  -- Convert the established cardinal equality into an equivalence of the underlying types.
  exact Cardinal.eq.mp positiveSequencesCardinalEqBinarySequences
