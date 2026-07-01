import Mathlib.RingTheory.Etale.QuasiFinite
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
* primary domain: quasi-finite finite-type algebra maps and their étale-local splitting at a
  chosen prime;
* sampled owner declarations:
  `Algebra.QuasiFiniteAt`,
  `Ideal.fiberIsoOfBijectiveResidueField`,
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`;
* best owner abstraction:
  the canonical mathlib theorem
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`;
* layer:
  this numbered item is direct `core/canonical` owner reuse, not a new source-facing wrapper;
* primitive data:
  a finite-type `R`-algebra `S`, primes `p ⊂ R` and `q ⊂ S` with `q` lying over `p`, and the
  hypothesis `[Algebra.QuasiFiniteAt R q]`;
* derived API:
  the étale neighborhood, the prime above `p`, the bijective residue-field map, and the
  idempotent cutting out the distinguished finite factor of `R' ⊗[R] S`.
-/

/- Lemma 10.145.2: let `R → S` be a finite type ring map, let `q ⊂ S` be a prime lying over
`p ⊂ R`, and assume `R → S` is quasi-finite at `q`. Then after passing to an étale
neighborhood `R → R'` with a prime `p'` over `p` and `κ(p') = κ(p)`, the base change
`R' ⊗[R] S` splits as a product `A × B` such that `A` is finite over `R'`, `A` has a unique
prime over `p'` lying over `q`, and `B` has no prime simultaneously lying over `p'` and `q`.
Mathlib packages this canonical decomposition by the equivalent idempotent-element form
`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`, where the product decomposition is
encoded by the idempotent corresponding to `(1, 0)`. -/
recall Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq
