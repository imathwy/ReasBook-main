import Mathlib

universe u v

-- Declarations for this item will be appended below by the statement pipeline.

section

variable (σ : Type v) (K : Type u) [CommRing K] [UniqueFactorizationMonoid K]

/- Theorem 1.3.51: the textbook field case is a specialization of mathlib's canonical owner
`MvPolynomial.uniqueFactorizationMonoid`, which is already stated at the weaker and more canonical
layer `[CommRing K] [UniqueFactorizationMonoid K]` for an arbitrary variable type `σ`. The earlier
monomial-order normalization into monic factors is a derived source-facing view, not the public
core abstraction. -/
#check (MvPolynomial.uniqueFactorizationMonoid σ :
  UniqueFactorizationMonoid (MvPolynomial σ K))

end
