import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Ideal

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsDomain S] [Algebra R S] [FaithfulSMul R S]
variable [Algebra.IsIntegral R S] [IsIntegrallyClosed R]

/- Domain triage:
* primary domain: going down for integral extensions of domains and prime ideals lying over one
  another;
* sampled owner declarations:
  `Algebra.HasGoingDown`,
  the integrally-closed-domain instance in
  `Mathlib.RingTheory.IntegralClosure.GoingDown`,
  `Ideal.exists_ideal_le_liesOver_of_le`,
  and the chapter-level recall style in `Lemma_10_39_19`;
* layer: `core/canonical` for the owner instance, with the textbook prime-lifting conclusion as
  derived `bridge/view` API.

Primitive-vs-derived split:
* primitive data: none in this file; Proposition 10.38.7 is a canonical recall item once the
  ambient hypotheses are in place;
* derived API: the source-facing existence statement for primes below a chosen `Q'`.
-/
/- Proposition 10.38.7 (Stacks tag `00H8`): let `R ⊆ S` be an inclusion of domains with `R`
normal and `S` integral over `R`. Then for primes `p ≤ p'` of `R` and any prime `Q'` of `S`
lying over `p'`, there exists a prime `Q ≤ Q'` of `S` lying over `p`; equivalently, the algebra
map `R → S` has going down. In mathlib this is the canonical instance
`Algebra.HasGoingDown R S`; the inclusion hypothesis `R ⊆ S` is encoded by `FaithfulSMul R S`,
and normality of the domain `R` is `IsIntegrallyClosed R`. This owner instance is unnamed, so the
direct canonical recall shape is instance synthesis of `Algebra.HasGoingDown R S`. The domain
structure on `R` is inferred from the faithful inclusion into the domain `S`. -/
#check (inferInstance : Algebra.HasGoingDown R S)

/- Companion recall: after instantiating the owner class above, the source-shaped prime-ideal
conclusion is the canonical theorem `Ideal.exists_ideal_le_liesOver_of_le`. -/
recall exists_ideal_le_liesOver_of_le
    [Algebra.HasGoingDown R S] {p p' : Ideal R} [p.IsPrime] [p'.IsPrime] (Q' : Ideal S)
    [Q'.IsPrime] [Q'.LiesOver p'] (hpp' : p ≤ p') : ∃ Q ≤ Q', Q.IsPrime ∧ Q.LiesOver p

end
