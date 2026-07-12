import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped PowerSeries

/- Proposition 5.1: the canonical unit criterion for formal power series is the owner theorem
`PowerSeries.isUnit_iff_constantCoeff`; over a field, its right-hand side is equivalent to the
textbook condition that the constant coefficient is nonzero. -/
recall PowerSeries.isUnit_iff_constantCoeff

namespace PowerSeries

/-- Proposition 5.1 in textbook form: a formal power series over a field is a unit if and only if
its constant coefficient is nonzero. -/
theorem isUnit_iff_constantCoeff_ne_zero {K : Type u} [Field K] {S : K⟦X⟧} :
    IsUnit S ↔ S.constantCoeff ≠ 0 := by
  -- Rewrite the unit condition for power series to the constant coefficient and then
  -- use the field criterion that a scalar is a unit exactly when it is nonzero.
  rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]

end PowerSeries
