import Mathlib
import stacks_project.Chap10.Definition_10_122_3

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling:
- primary domain: local quasi-finiteness for finite-type unramified algebra maps;
- sampled owner declarations:
  `Algebra.IsUnramifiedAt`,
  `Algebra.QuasiFiniteAt`,
  `Algebra.FiniteType.QuasiFiniteAt`,
  `Algebra.FiniteType.QuasiFiniteAt.of_quasiFiniteAt`;
- best owner abstraction: the chapter's source-facing owner
  `Algebra.FiniteType.QuasiFiniteAt`, whose mathematical core is the canonical local owner
  `Algebra.QuasiFiniteAt`;
- source/core/bridge triage:
  `source-facing`: `Algebra.FiniteType.QuasiFiniteAt R S q` from Definition `10.122.3`;
  `core/canonical`: `Algebra.QuasiFiniteAt R q`;
  `bridge/view`: `Algebra.FiniteType.QuasiFiniteAt.of_quasiFiniteAt`;
- primitive data vs derived API: finite type and `Algebra.IsUnramifiedAt R q` are the primitive
  hypotheses. The quasi-finite conclusion is already the canonical owner instance
  `Algebra.QuasiFiniteAt R q`, and the chapter source-facing predicate is derived from it via the
  bridge in Definition `10.122.3`.
-/

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

open Algebra.FiniteType.QuasiFiniteAt

/- Under an ambient finite-type hypothesis, Definition `10.122.3` packages the canonical local
owner as the chapter's source-facing quasi-finite predicate. -/
#check of_quasiFiniteAt

variable [Algebra.FiniteType R S]
variable (q : Ideal S) [q.IsPrime] [Algebra.IsUnramifiedAt R q]

/- Companion recall: unramifiedness at `q` already gives the canonical local owner
`Algebra.QuasiFiniteAt R q`. -/
#check (inferInstance : Algebra.QuasiFiniteAt R q)

/-- Lemma 10.151.6: for a finite-type algebra map, unramifiedness at `q` implies the source-facing
quasi-finite predicate of Definition `10.122.3`. -/
theorem quasiFiniteAt_of_isUnramifiedAt : Algebra.FiniteType.QuasiFiniteAt R S q :=
  of_quasiFiniteAt (inferInstance : Algebra.QuasiFiniteAt R q)

end
