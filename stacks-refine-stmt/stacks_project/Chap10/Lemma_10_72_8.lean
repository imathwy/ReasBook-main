import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Domain triage:
* primary domain: commutative algebra of associated primes of finite modules over a Noetherian
  ring, with passage to quotients by powers of a principal ideal;
* sampled owner declarations of the same kind:
  `associatedPrimes R M`,
  `Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes`,
  `associatedPrimes.subset_of_injective`,
  `Submodule.exists_eq_colon_of_mem_minimalPrimes`;
* best owner abstraction: mathlib's owner set `associatedPrimes`, together with the canonical
  quotient object `QuotSMulTop (x ^ n) M`;
* primitive data: only the module `M`, the element `x`, the associated prime `p`, the minimal
  prime `q`, and the quotient modules `QuotSMulTop (x ^ n) M`;
* derived API: passage from minimal primes over annihilators to associated-prime membership, and
  inclusion of associated primes along the cyclic-submodule image in the quotient.

This numbered item is `source-facing`, but it already lives directly on the owner abstraction
`associatedPrimes`; there is no smaller local wrapper to keep or introduce here.
-/

/-- Lemma 10.72.8: if `p` is an associated prime of a finite module `M` over a Noetherian ring
`R`, and if `q` is minimal over `p + (x)`, then `q` is an associated prime of `M / x^n M`,
written canonically as `QuotSMulTop (x ^ n) M`, for some `n ≥ 1`. -/
-- Proof sketch: choose a cyclic submodule `N ⊆ M` isomorphic to `R ⧸ p` realizing `p` as an
-- associated prime. Artin-Rees gives `n > 0` with `N ∩ (Ideal.span {x}) ^ n • ⊤ ⊆ xN`. The image
-- of `N` in `QuotSMulTop (x ^ n) M` then surjects onto `N / xN ≅ R ⧸ (p ⊔ Ideal.span {x})`,
-- so `q` lies in its support. Since that image is annihilated by both `p` and `x^n`, the prime
-- `q` is minimal in its support, hence associated by the owner minimal-support criterion; finally
-- apply `associatedPrimes.subset_of_injective` to the cyclic-submodule image inside the ambient
-- quotient.
theorem exists_mem_associatedPrimes_quotient_span_singleton_pow_of_mem_minimalPrimes_sup
    (x : R) (p q : Ideal R)
    (hp : p ∈ associatedPrimes R M)
    (hq : q ∈ (p ⊔ Ideal.span {x}).minimalPrimes) :
    ∃ n : ℕ, 0 < n ∧ q ∈ associatedPrimes R (QuotSMulTop (x ^ n) M) := sorry

end
