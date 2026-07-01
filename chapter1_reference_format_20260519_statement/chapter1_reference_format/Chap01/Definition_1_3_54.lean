import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 1.3.54: a multivariable polynomial is symmetric when every permutation of its
variables leaves it unchanged; mathlib's canonical predicate for this notion is
`MvPolynomial.IsSymmetric`. -/
recall MvPolynomial.IsSymmetric {σ : Type u} {R : Type v} [CommSemiring R]
  (φ : MvPolynomial σ R) : Prop
