import Mathlib.Algebra.Order.Hom.MonoidWithZero
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

/- Definition 10.50.13: for a valuation ring `A`, the value group is the ordered abelian group
`Γ = Kˣ / Aˣ`. In mathlib, this group is represented by the unit group of the canonical owner
object `ValuationRing.ValueGroup A (FractionRing A)`. -/
#check (ValuationRing.ValueGroup A (FractionRing A))ˣ

end

/- Companion recall: the valuation associated to a valuation ring is the canonical valuation
`ValuationRing.valuation A (FractionRing A)` on its fraction field; its codomain is the with-zero
version of the value group from Definition 10.50.13, and restricting this map to
`A \ {0}` or to `(FractionRing A)ˣ` gives the textbook maps `v : A - \{0\} → Γ` and
`v : K^* → Γ`. -/
recall ValuationRing.valuation

/- Companion recall: adjoining `0` to the ordered abelian group from Definition 10.50.13 recovers
the canonical with-zero value group used by `ValuationRing.valuation`. -/
recall OrderMonoidIso.withZeroUnits

/- Companion recall: the further textbook condition that the value group be infinite cyclic is
formalized in mathlib by the standard predicate `IsDiscreteValuationRing A`. The corresponding
normalization of the associated with-zero value group by `ℤᵐ⁰` belongs to the separate
rank-one-discrete valuation API, not to the present definition of the value group itself. -/
recall IsDiscreteValuationRing

/- Companion recall: once `A` is a discrete valuation ring, the associated valuation on its
fraction field is canonically rank-one discrete. This is the bridge from the present value-group
definition to the `ℤᵐ⁰` normalization API. -/
recall IsDiscreteValuationRing.isRankOneDiscrete
