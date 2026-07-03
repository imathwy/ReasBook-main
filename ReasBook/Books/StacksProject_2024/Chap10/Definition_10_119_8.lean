import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Ideal IsLocalRing

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/- Definition 10.119.8 is a `bridge/view` item: in a discrete valuation ring, the textbook
condition that `π` generate the maximal ideal is already the conclusion of the canonical owner
theorem `IsDiscreteValuationRing.irreducible_iff_uniformizer`, and mathlib deliberately uses
`Irreducible π` rather than a second public `IsUniformizer` predicate. -/
recall IsDiscreteValuationRing.irreducible_iff_uniformizer

/-- Companion bridge for Definition 10.119.8: in a discrete valuation ring, the textbook
uniformizer condition `maximalIdeal A = Ideal.span {π}` is equivalent to the canonical owner
predicate `Irreducible π`. -/
theorem maximalIdeal_eq_span_singleton_iff_irreducible (π : A) :
    maximalIdeal A = Ideal.span {π} ↔ Irreducible π := by
  simpa using (IsDiscreteValuationRing.irreducible_iff_uniformizer π).symm

end
