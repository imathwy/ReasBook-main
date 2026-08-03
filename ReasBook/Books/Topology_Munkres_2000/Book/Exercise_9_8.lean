module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Data.PNat.Basic

public section

/-- Exercise 9.8: The power set of the positive integers and the real numbers have
the same cardinality. -/
theorem positiveIntegerPowerSetEquivReal : Nonempty (Set ℕ+ ≃ ℝ) := by
  -- Translate existence of an equivalence into equality of lifted cardinalities.
  rw [← Cardinal.lift_mk_eq']
  -- Both cardinalities reduce to the continuum `2 ^ ℵ₀`.
  simp only [Cardinal.lift_uzero, Cardinal.mk_set, Cardinal.mk_pnat,
    Cardinal.two_power_aleph0, Cardinal.mk_real]

/-- The cardinal-arithmetic form of `positiveIntegerPowerSetEquivReal`. -/
theorem positiveIntegerPowerSet_cardinality :
    Cardinal.mk (Set ℕ+) = Cardinal.mk ℝ := by
  rcases positiveIntegerPowerSetEquivReal with ⟨e⟩
  exact Cardinal.mk_congr e
