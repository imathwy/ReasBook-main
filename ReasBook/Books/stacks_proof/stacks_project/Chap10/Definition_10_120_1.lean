import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain triage:
- primary domain: commutative algebra of associated, irreducible, and prime elements, together
  with the principal-ideal reformulation of primality;
- sampled owner declarations: `Associated`, `Irreducible`, `Prime`,
  and `Ideal.span_singleton_prime`;
- best owner abstraction: the mathlib owners `Associated`, `Irreducible`, and `Prime`, with the
  bridge to prime principal ideals given by `Ideal.span_singleton_prime`;
- layer: `core/canonical`, since Definition 10.120.1 is only recalling standard owner notions
  already present in mathlib;
- primitive data: an ambient monoid or commutative monoid with zero element;
- derived API: the principal-ideal characterization of prime elements.
-/

/- Definition 10.120.1 is a `core/canonical` recall item: the textbook notions of associated
elements, irreducible elements, and prime elements are already owned in mathlib by
`Associated`, `Irreducible`, and `Prime`, and the principal-ideal reformulation of prime elements
is the canonical theorem `Ideal.span_singleton_prime`. -/
recall Associated
recall Irreducible
recall Prime
recall Ideal.span_singleton_prime
