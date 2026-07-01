import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PowerSeries

universe u

variable {R : Type u} [CommRing R]

namespace PowerSeries

/-- Remark I.1-extra-8: substituting the zero formal power series into
`S(X) = ∑ n ≥ 0, aₙ X^n` leaves only the constant term, so the resulting formal series is the
constant series `a₀`. -/
theorem subst_zero (S : R⟦X⟧) : S.subst (0 : R⟦X⟧) = C S.constantCoeff := by
  simpa using (rescale_eq_subst 0 S).symm.trans (rescale_zero_apply S)

end PowerSeries

attribute [simp] PowerSeries.subst_zero
