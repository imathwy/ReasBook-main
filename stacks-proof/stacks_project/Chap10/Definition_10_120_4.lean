import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.120.4 is a `core/canonical` recall item: the textbook notion of a unique
factorization domain is owned in mathlib by `UniqueFactorizationMonoid`. For a domain `R`, this
packages existence and uniqueness of irreducible factorizations up to reordering and associates. -/
recall UniqueFactorizationMonoid

/- Companion recall: `UniqueFactorizationMonoid.exists_prime_factors` is derived API from the owner
class; it produces prime factors whose product is associated to the given nonzero element. -/
recall UniqueFactorizationMonoid.exists_prime_factors

/- Companion recall: `UniqueFactorizationMonoid.factors_unique` is the derived uniqueness theorem
comparing two irreducible factorizations via `Multiset.Rel Associated`. -/
recall UniqueFactorizationMonoid.factors_unique
