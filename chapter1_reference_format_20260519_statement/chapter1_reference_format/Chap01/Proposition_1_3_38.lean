import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Polynomial

/- Proposition 1.3.38: if a polynomial over an infinite field vanishes at every point, then it is
the zero polynomial. Mathlib proves this in the more general setting of an infinite integral
domain as `Polynomial.zero_of_eval_zero`; the field case is a specialization. -/
recall Polynomial.zero_of_eval_zero {R : Type u} [CommRing R] [IsDomain R] [Infinite R]
  (p : R[X]) (h : ∀ x : R, p.eval x = 0) : p = 0
