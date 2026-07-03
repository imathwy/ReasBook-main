import StacksProject_2024.Chap10.Definition_10_63_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage: this item lies in commutative algebra of associated primes of modules.
Sampled declarations in this domain are the chapter's source-facing `associatedPrimesOfModule`,
the bridge `associatedPrimesOfModule_eq_associatedPrimes`, and mathlib's owner lemmas
`associatedPrimes.eq_empty_of_subsingleton` and `associatedPrimes.nonempty`. The numbered item is
`source-facing`, while the owner-form statement is only a derived `bridge/view` companion in the
Noetherian setting. -/

/-- Lemma 10.63.7: over a Noetherian ring, an `R`-module `M` is the zero module exactly when
its textbook set of associated primes is empty. In Lean, `M = (0)` is expressed as
`Subsingleton M`. -/
-- Proof sketch: pass from the source-facing set `associatedPrimesOfModule` to the Noetherian
-- owner set `associatedPrimes` via `associatedPrimesOfModule_eq_associatedPrimes`, then use
-- `associatedPrimes.eq_empty_of_subsingleton` and `associatedPrimes.nonempty`.
theorem subsingleton_iff_associatedPrimesOfModule_eq_empty :
    Subsingleton M ↔ associatedPrimesOfModule R M = ∅ := by
  constructor
  · intro hM
    letI := hM
    rw [associatedPrimesOfModule_eq_associatedPrimes]
    simpa using (associatedPrimes.eq_empty_of_subsingleton : associatedPrimes R M = ∅)
  · intro hAssoc
    by_contra hM
    letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    have hAssoc' : associatedPrimes R M = ∅ := by
      simpa [associatedPrimesOfModule_eq_associatedPrimes] using hAssoc
    exact (associatedPrimes.nonempty R M).ne_empty hAssoc'

/-- Noetherian owner-form companion to Lemma 10.63.7 in mathlib's `associatedPrimes` API. -/
theorem subsingleton_iff_associatedPrimes_eq_empty :
    Subsingleton M ↔ associatedPrimes R M = ∅ := by
  simpa [associatedPrimesOfModule_eq_associatedPrimes] using
    (subsingleton_iff_associatedPrimesOfModule_eq_empty :
      Subsingleton M ↔ associatedPrimesOfModule R M = ∅)

end
