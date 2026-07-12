import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/- Domain triage:
* primary domain: going down for commutative algebras and prime ideals lying over one another;
* sampled owner declarations:
  `Algebra.HasGoingDown`,
  `Algebra.HasGoingDown.of_flat`,
  `Ideal.exists_ideal_lt_liesOver_of_lt`,
  and the chapter-level owner recall in `Definition_10_41_1`;
* layer: `core/canonical` for the owner instance, with the source-shaped strict prime-lifting
  statement as derived `bridge/view` API.

Primitive-vs-derived split:
* primitive data: none; the source content is carried by the owner predicate
  `Algebra.HasGoingDown R S` under the ambient flatness hypothesis;
* derived API: the existence of a strict prime below a chosen `q'` lying over `p'`.
-/
/- Lemma 10.39.19: flat algebras satisfy the canonical going-down property
`Algebra.HasGoingDown R S`. This owner instance is exactly `Algebra.HasGoingDown.of_flat`. -/
recall Algebra.HasGoingDown.of_flat

/- Companion recall: after instantiating the owner theorem above, the textbook strict
prime-ideal conclusion is the canonical theorem `Ideal.exists_ideal_lt_liesOver_of_lt`. -/
recall Ideal.exists_ideal_lt_liesOver_of_lt

end
