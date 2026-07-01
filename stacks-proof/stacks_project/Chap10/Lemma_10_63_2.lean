import stacks_project.Chap10.Definition_10_63_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-
Domain triage: this item lies in commutative algebra of associated primes and module support.
The owner abstraction is mathlib's `IsAssociatedPrime` / `associatedPrimes R M`, while the
textbook exact-annihilator set `associatedPrimesOfModule R M` from Definition 10.63.1 is the
source-facing bridge layer.
-/

/-- A mathlib-associated prime of an `R`-module lies in its support. -/
theorem IsAssociatedPrime.mem_support {𝔭 : Ideal R} (h𝔭 : IsAssociatedPrime 𝔭 M) :
    (⟨𝔭, h𝔭.isPrime⟩ : PrimeSpectrum R) ∈ Module.support R M := by
  rcases h𝔭.eq_radical_colon with ⟨m, hm⟩
  rw [Module.mem_support_iff_exists_annihilator]
  refine ⟨m, ?_⟩
  simpa [Submodule.bot_colon', hm] using
    (Ideal.le_radical :
      (⊥ : Submodule R M).colon ({m} : Set M) ≤
        ((⊥ : Submodule R M).colon ({m} : Set M)).radical)

namespace Module

/-- Canonical owner-form of Lemma 10.63.2 for mathlib's radical-based `associatedPrimes R M`. -/
theorem associatedPrimes_subset_support :
    PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M ⊆ support R M := by
  intro 𝔭 h𝔭
  simpa using (AssociatedPrimes.mem_iff.mp h𝔭).mem_support

/-- Lemma 10.63.2: every textbook-associated prime of an `R`-module `M` lies in the support
`Module.support R M`. -/
-- Proof sketch: if `p ∈ associatedPrimesOfModule R M`, then by Definition 10.63.1 there is
-- `m : M` with `p = Ideal.torsionOf R M m = (R ∙ m).annihilator`, and
-- `Module.mem_support_iff_exists_annihilator` puts the corresponding point of `Spec R` in
-- `Supp(M)`.
theorem associatedPrimesOfModule_subset_support :
    PrimeSpectrum.asIdeal ⁻¹' associatedPrimesOfModule R M ⊆ support R M := by
  intro 𝔭 h𝔭
  exact associatedPrimes_subset_support <|
    associatedPrimesOfModule_subset_associatedPrimes R M h𝔭

end Module
