import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Polynomial

variable {R : Type u} [Semiring R] [NoZeroDivisors R]

/-- Proposition 1.3.2: a polynomial is invertible if and only if it is a constant polynomial
`C a` coming from a unit `a : Rˣ`.

The textbook states this over a field; the same source-facing characterization already holds at the
canonical owner level `[Semiring R] [NoZeroDivisors R]`. Over a field, this recovers the usual
description that the units of `R[X]` are exactly the nonzero constant polynomials. -/
-- Proof sketch: this is a source-facing companion of the canonical owner theorem
-- `Polynomial.isUnit_iff`. A unit polynomial is a constant polynomial `C a` with `a` a unit in
-- `R`, hence with bundled witness `a : Rˣ`; conversely `Polynomial.isUnit_C` shows that every
-- constant polynomial coming from a unit of `R` is a unit.
theorem polynomial_isUnit_iff_eq_C_unit {p : R[X]} :
    IsUnit p ↔ ∃ a : Rˣ, p = C (a : R) := by
  constructor
  · intro hp
    rcases Polynomial.isUnit_iff.mp hp with ⟨a, ha, rfl⟩
    exact ⟨ha.unit, rfl⟩
  · rintro ⟨a, rfl⟩
    exact Polynomial.isUnit_C.mpr a.isUnit
