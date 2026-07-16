import stacks_proof.stacks_project.Chap10.Lemma_10_125_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']
variable [Algebra.FiniteType R S]

local notation "baseChangeComap" =>
  PrimeSpectrum.comap (includeRight.toRingHom : S →+* (R' ⊗[R] S))

/-- Chap10 Lemma 10 125 7 (Tag `00QI`): for a finite type ring map `R → S`, an arbitrary base
change `R → R'`, and `S' = R' ⊗[R] S`, the inverse image in `Spec(S')` of the locus of primes
`q : Spec(S)` where the corresponding point of the fiber `Spec(κ(q ∩ R) ⊗[R] S)` has local
topological dimension at most `n` is exactly the analogous locus in `Spec(S')`. -/
@[stacks 00QI]
theorem relativeDimensionAt_le_preimage_eq_baseChange (n : ℕ) :
    baseChangeComap ⁻¹'
        { q : PrimeSpectrum S |
          topologicalKrullDimAt (fiberPrimeAt R S q) ≤ (n : WithBot ℕ∞) } =
      { q' : PrimeSpectrum (R' ⊗[R] S) |
        topologicalKrullDimAt (fiberPrimeAt R' (R' ⊗[R] S) q') ≤ (n : WithBot ℕ∞) } := sorry

end
