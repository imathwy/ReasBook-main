import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]

/- Domain-style sampling for Lemma 10.37.8:
- primary domain: integrally closed domains and polynomial extensions in commutative algebra
- sampled owner declarations:
  `IsIntegrallyClosed`,
  `isIntegrallyClosed_iff_isIntegrallyClosedIn`,
  `IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn`,
  `instIsIntegrallyClosedPolynomialOfIsDomain`
- canonical owner abstraction: `IsIntegrallyClosed`
- primitive data: the ambient commutative-domain structure on `R` together with
  `[IsIntegrallyClosed R]`
- derived API: the induced integrally closed instance on `R[X]`

Layer triage:
- `source-facing`: the textbook assertion that a polynomial ring over a normal domain is normal
- `core/canonical`: the mathlib instance `instIsIntegrallyClosedPolynomialOfIsDomain`
- `bridge/view`: none; the source statement is already exactly owner-shaped

This numbered item adds no new data beyond the canonical owner instance, so a local theorem or
alias would only duplicate the upstream API.
-/
/- Lemma 10.37.8: if `R` is a normal domain, then the polynomial ring `R[X]` is again a normal
domain. By Definition 10.37.1, the owner notion of normality is `IsIntegrallyClosed`, and the
polynomial-ring conclusion is exactly the canonical derived instance
`instIsIntegrallyClosedPolynomialOfIsDomain : IsIntegrallyClosed (Polynomial R)`. -/
recall instIsIntegrallyClosedPolynomialOfIsDomain
