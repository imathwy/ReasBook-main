import Mathlib

open scoped PowerSeries

universe u

variable (A : Type u) [CommRing A] [IsDomain A]

/- Remark I.1-extra-6: the existing instance `IsDomain A⟦X⟧` records that formal power series
with coefficients in a commutative ring `A` with `1`, not necessarily a field, again form an
integral domain whenever `A` is an integral domain. -/
#check (inferInstance : IsDomain A⟦X⟧)
