import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/- Domain-style sampling for normal domains:
- primary domain: integrally closed domains in commutative algebra
- sampled owner declarations:
  `IsIntegrallyClosed`,
  `isIntegrallyClosed_iff_isIntegrallyClosedIn`,
  `IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn`,
  `isIntegrallyClosed_of_isLocalization`
- canonical owner abstraction: `IsIntegrallyClosed`
- primitive data: the ambient commutative-domain structure on `R`
- derived API: alternate fraction-field formulations, localization stability, and integral-closure
  transfer lemmas

Layer triage:
- `source-facing`: the Stacks definition that a domain is normal
- `core/canonical`: mathlib's `IsIntegrallyClosed`
- `bridge/view`: fraction-field and localization reformulations of integrally closedness

This numbered item adds no new data beyond the canonical owner, so keeping a chapter-local alias or
an `_iff` theorem as the main public entry would only duplicate the upstream API.
-/
/- Definition 10.37.1: a domain `R` is normal if it is integrally closed in its field of
fractions. This source-facing item is a direct recall of the mathlib owner predicate
`IsIntegrallyClosed R`; the primitive ambient data are just the commutative ring/domain
assumptions. -/
recall IsIntegrallyClosed
