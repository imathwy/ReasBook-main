import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/- 
Domain-style sampling:
- primary domain: principal ideal domains and Dedekind domains;
- sampled owner API:
  `IsDedekindDomain`,
  `IsPrincipalIdealRing`,
  `IsPrincipalIdealRing.isDedekindDomain`,
  `isDedekindDomain_iff`;
- source-facing: the textbook implication that a principal ideal domain is a Dedekind domain;
- core/canonical: the owner class `IsDedekindDomain`;
- bridge/view: the instance `IsPrincipalIdealRing.isDedekindDomain`.

Primitive data are exactly the PID hypotheses `[IsDomain R] [IsPrincipalIdealRing R]`. The
Dedekind-domain structure is derived API already owned upstream, so this file should recall that
owner instance directly and not introduce any parallel local wrapper or restatement.
-/

/- Lemma 10.120.15: a principal ideal domain is a Dedekind domain. This is exactly the canonical
mathlib instance `IsPrincipalIdealRing.isDedekindDomain`. -/
recall IsPrincipalIdealRing.isDedekindDomain
