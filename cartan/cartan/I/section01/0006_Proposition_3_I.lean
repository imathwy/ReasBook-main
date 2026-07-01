import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PowerSeries

universe u

section

variable (K : Type u) [Field K]

/- Proposition 3.I: for a field `K`, the formal power series ring `K⟦X⟧` carries the canonical
integral-domain structure coming from the `IsDomain` instance on power series over a domain. -/
#check (inferInstance : IsDomain K⟦X⟧)

/- Equivalently, the product of two nonzero formal power series over `K` is nonzero. -/
#check (mul_ne_zero : ∀ {f g : K⟦X⟧}, f ≠ 0 → g ≠ 0 → f * g ≠ 0)

end
