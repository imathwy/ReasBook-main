import Mathlib
import StacksProject_2024.Chap10.Definition_10_112_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

/-- Definition 10.125.1 (1): for a prime `q : Spec S`, the relative dimension of `S/R` at `q`
is the Krull dimension of the local ring of the fiber `κ(q ∩ R) ⊗[R] S` at the prime
corresponding to `q`. -/
noncomputable abbrev relativeDimensionAt (q : PrimeSpectrum S) : WithBot ℕ∞ :=
  ringKrullDim (fiberLocalRingAt R S q)

/-- Definition 10.125.1 (2): the relative dimension of `S/R` is the supremum of the relative
dimensions at all primes `q : Spec S`. -/
noncomputable abbrev relativeDimension : WithBot ℕ∞ :=
  ⨆ q : PrimeSpectrum S, relativeDimensionAt R S q

end
