import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Polynomial

variable {R : Type u} [Semiring R]

/- Lemma 1.3.1 (1): the canonical degree function on polynomials satisfies
`deg (F + G) ≤ max {deg F, deg G}`. -/
recall Polynomial.degree_add_le (p q : R[X]) :
  (p + q).degree ≤ max p.degree q.degree

/- Lemma 1.3.1 (2): the canonical degree function on polynomials satisfies
`deg (F G) = deg F + deg G`. -/
recall Polynomial.degree_mul [NoZeroDivisors R] {p q : R[X]} :
  (p * q).degree = p.degree + q.degree
