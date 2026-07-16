import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_103_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: argue by induction on `ringKrullDim R`. For positive dimension, use prime
-- avoidance to choose `x ∈ p₁` outside the minimal primes, pass to `R / xR` and `M / xM`, apply
-- the Cohen-Macaulay quotient lemmas to keep full support, identify `p₁ / (x)` as a minimal prime
-- of the quotient, and then apply the induction hypothesis to the induced maximal chain there.
/-- Lemma 10.103.9: if `R` is a Noetherian local ring and `M` is a finite `R`-module whose support
is all of `Spec R` and whose depth equals the dimension of its support, then every maximal chain
of prime ideals of `R`, encoded as an `LTSeries` with maximal range, has length `ringKrullDim R`.
-/
theorem ringKrullDim_eq_length_of_maximal_prime_chain_of_full_support_cohenMacaulay
    (hCM : Module.CohenMacaulay R M) (hsupp : Module.support R M = Set.univ)
    (p : LTSeries (PrimeSpectrum R))
    (hp : IsMaxChain (· ≤ ·) (Set.range p)) :
    ringKrullDim R = p.length := sorry

end
