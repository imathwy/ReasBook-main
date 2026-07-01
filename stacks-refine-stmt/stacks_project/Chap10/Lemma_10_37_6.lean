import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/- Lemma 10.37.6: a principal ideal domain is normal, i.e. it is integrally closed in its
fraction field. The owner abstraction here is the canonical typeclass `IsIntegrallyClosed R`,
while the primitive source data are just the PID hypotheses. A PID canonically carries a
`GCDMonoid` structure, so this is the direct upstream bridge `GCDMonoid.toIsIntegrallyClosed`. -/
recall GCDMonoid.toIsIntegrallyClosed
