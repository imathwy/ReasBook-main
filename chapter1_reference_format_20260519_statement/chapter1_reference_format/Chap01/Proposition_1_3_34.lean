import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Polynomial

/- Proposition 1.3.34: for `a ∈ K` and `P ∈ K[X]`, divisibility by the linear factor `X - a`
is equivalent to saying that `a` is a root of `P`. Mathlib proves this criterion in the more
general setting of a commutative coefficient ring, and the field case is a specialization of
`Polynomial.dvd_iff_isRoot`. -/
recall Polynomial.dvd_iff_isRoot {R : Type u} {a : R} [CommRing R] {p : R[X]} :
  X - C a ∣ p ↔ p.IsRoot a
