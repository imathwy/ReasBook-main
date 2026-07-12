import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/- 
Domain-style sampling:
- primary domain: factorization theory for principal ideal domains and unique factorization domains;
- sampled owner API:
  `IsPrincipalIdealRing`,
  `UniqueFactorizationMonoid`,
  `PrincipalIdealRing.to_uniqueFactorizationMonoid`,
  `IsPrincipalIdealRing.isDedekindDomain`;
- source-facing: the textbook implication that a principal ideal domain is a unique factorization
  domain;
- core/canonical: the mathlib owner classes `IsPrincipalIdealRing` and `UniqueFactorizationMonoid`;
- bridge/view: the instance `PrincipalIdealRing.to_uniqueFactorizationMonoid`.

Primitive data are exactly the PID hypotheses `[IsDomain R] [IsPrincipalIdealRing R]`. The UFD
structure is derived API owned upstream, so this file should recall that owner instance directly
and not introduce any parallel wrapper or local restatement.
-/

/- Lemma 10.120.13: a principal ideal domain is a unique factorization domain. This is exactly the
canonical mathlib instance `PrincipalIdealRing.to_uniqueFactorizationMonoid`. -/
recall PrincipalIdealRing.to_uniqueFactorizationMonoid
