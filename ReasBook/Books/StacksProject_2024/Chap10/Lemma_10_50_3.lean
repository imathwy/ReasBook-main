import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Valuation.ValuationRing

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]

/- Lemma 10.50.3: let `A` be a valuation ring. Then `A` is a normal domain. This is a
`bridge/view` use of the chapter's owner predicate `IsIntegrallyClosed A`: the primitive data are
the commutative-domain and valuation-ring assumptions, while normality itself is the derived
canonical instance obtained upstream from the induced `IsBezout A` structure. -/
#check (inferInstance : IsIntegrallyClosed A)

end
