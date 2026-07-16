import stacks_proof.stacks_project.Chap10.Definition_10_64_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Lemma 10.64.2: for a prime ideal `𝔭` of a Noetherian ring `R` and `n > 0`, the associated
primes of `R ⧸ 𝔭^(n)` are exactly `{𝔭}`, where `𝔭^(n)` is the symbolic power from
Definition `10.64.1`. -/
-- Proof sketch: `symbolicPower 𝔭 n` is a `𝔭`-primary ideal for `n > 0`, so
-- `associatedPrimes.eq_singleton_of_isPrimary` identifies the associated primes of the quotient by
-- this ideal with the singleton consisting of its radical, which is `𝔭`.
@[stacks 0314]
theorem associatedPrimes_quotient_symbolicPower_eq_singleton (𝔭 : Ideal R) [𝔭.IsPrime] {n : ℕ}
    (hn : 0 < n) :
    associatedPrimes R (R ⧸ 𝔭.symbolicPower n) = {𝔭} := by
  simpa [Ideal.radical_symbolicPower 𝔭 hn] using
    associatedPrimes.eq_singleton_of_isPrimary (Ideal.symbolicPower_isPrimary 𝔭 hn)

end
