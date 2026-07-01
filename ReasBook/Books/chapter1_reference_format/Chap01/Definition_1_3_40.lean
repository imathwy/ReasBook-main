import Mathlib

open Polynomial

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.3.40: a polynomial over a field splits over that field when it factors as a
constant times a finite product of linear factors over the field; mathlib's canonical
predicate for this notion is `Polynomial.Splits`. -/
recall Polynomial.Splits {R : Type u} [Semiring R] (f : Polynomial R) : Prop

variable {K : Type u} [Field K]

/- Over a field, `Polynomial.Splits` is equivalent to being a constant times a finite product of
linear factors `X - a`; repeated factors in the multiset encode the positive exponents `r_i` from
the textbook factorization. -/
#check (Polynomial.splits_iff_exists_multiset :
  ∀ {f : K[X]}, f.Splits ↔ ∃ m : Multiset K,
    f = C f.leadingCoeff * (m.map (X - C ·)).prod)
