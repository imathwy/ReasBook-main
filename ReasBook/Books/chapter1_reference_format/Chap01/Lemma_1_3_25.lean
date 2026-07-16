import Mathlib
import chapter1_reference_format.Chap01.Proposition_1_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

/-- Lemma 1.3.25: every unit of the polynomial ring `ℤ[X]` is either `1` or `-1`, so the
multiplicative group of `ℤ[X]` is exactly `{±1}`. -/
-- Proof sketch: use `Polynomial.isUnit_iff` to show that a unit of `ℤ[X]` is a constant
-- polynomial `C r` with `r` a unit of `ℤ`; then apply `Int.units_eq_one_or` to the corresponding
-- integer unit and rewrite the constant polynomial as `1` or `-1`.
theorem int_polynomial_units_eq_one_or (u : ℤ[X]ˣ) : u = 1 ∨ u = -1 := by
  rcases polynomial_isUnit_iff_eq_C_unit.mp u.isUnit with ⟨a, ha⟩
  rcases Int.units_eq_one_or a with rfl | rfl
  · left
    apply Units.ext
    simpa using ha
  · right
    apply Units.ext
    simpa using ha
