import StacksProject_2024.Chap10.Lemma_10_63_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/- Domain triage: this item is in commutative algebra of associated primes under restriction of
scalars.
* `source-facing`: the textbook set `associatedPrimesOfModule R M`.
* `core/canonical`: mathlib's owner set `associatedPrimes R M`.
* `bridge/view`: contraction along `Spec(S) → Spec(R)` induced by `algebraMap R S`.
The textbook statement is source-facing, while the owner-form companion is kept as a thin
Noetherian bridge for downstream use. -/

/-- Lemma 10.63.13: if `S` is Noetherian, then contracting the textbook associated primes
`Ass_S(M)` along `Spec(S) → Spec(R)` gives exactly the textbook associated primes `Ass_R(M)`. -/
-- Proof sketch: Lemma 10.63.11 gives the inclusion from left to right. For the reverse
-- inclusion, choose `p ∈ Ass_R(M)` coming from an element `m : M`, let `I` be the annihilator of
-- `m` in `S`, and choose a prime `q` minimal over `I` that contracts to `p`. Since `S` is
-- Noetherian, minimal primes over annihilators are associated, so `q ∈ Ass_S(M)` and contracts
-- to `p`.
theorem associatedPrimesOfModule_restrictScalars_eq_image_comap [IsNoetherianRing S] :
    Ideal.comap (algebraMap R S) '' associatedPrimesOfModule S M =
      associatedPrimesOfModule R M := sorry

/-- Noetherian owner-form companion to Lemma 10.63.13 in mathlib's `associatedPrimes` API. -/
-- Proof sketch: rewrite the source-facing equality through
-- `associatedPrimesOfModule_eq_associatedPrimes` on both sides, using that over a Noetherian ring
-- the textbook exact-annihilator notion agrees with mathlib's radical-based `associatedPrimes`.
theorem associatedPrimes_restrictScalars_eq_image_comap [IsNoetherianRing S] :
    Ideal.comap (algebraMap R S) '' associatedPrimes S M =
      associatedPrimes R M := sorry

end
