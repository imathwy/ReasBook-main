import Mathlib
import StacksProject_2024.Chap10.Definition_10_66_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage: this item lies in commutative algebra of weakly associated primes of modules.
The owner abstraction is the project declaration `weaklyAssociatedPrimes R M` from
`Definition_10_66_1`, modeled on mathlib's `associatedPrimes`. The owner-level API
`weaklyAssociatedPrimes.eq_empty_of_subsingleton` and `weaklyAssociatedPrimes.nonempty` now lives
with that owner declaration, and the theorem below is the source-facing bridge identifying
vanishing of the owner set with triviality of the module. -/

/-- Lemma 10.66.5: an `R`-module `M` is the zero module if and only if its set of weakly
associated primes is empty. -/
-- Proof sketch: if `M` is subsingleton, every element is zero, so there is no annihilator of a
-- nonzero element from which a weakly associated prime could arise. Conversely, if `M` is not
-- subsingleton, choose a nonzero element `m : M`; then `R / ann(m)` embeds into `M`, so Lemma
-- 10.66.4 reduces the claim to finding a minimal prime over `ann(m)`, which exists because
-- `ann(m) ≠ ⊤` and hence `Spec (R / ann(m))` is nonempty by Lemmas 10.17.2 and 10.17.7.
theorem subsingleton_iff_weaklyAssociatedPrimes_eq_empty :
    Subsingleton M ↔ weaklyAssociatedPrimes R M = ∅ := by
  constructor
  · intro h
    letI := h
    simpa using
      (weaklyAssociatedPrimes.eq_empty_of_subsingleton : weaklyAssociatedPrimes R M = ∅)
  · intro h
    by_contra hM
    letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    exact (weaklyAssociatedPrimes.nonempty : (weaklyAssociatedPrimes R M).Nonempty).ne_empty h

end
