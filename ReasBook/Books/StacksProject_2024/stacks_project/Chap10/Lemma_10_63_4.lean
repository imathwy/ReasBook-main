import StacksProject_2024.Chap10.Definition_10_63_1
import StacksProject_2024.Chap10.Lemma_10_62_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum RelSeries Submodule

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (s : PrimeCyclicFiltration R M)

/-
Domain triage:
- primary domain: commutative algebra of associated primes and prime-cyclic filtrations;
- source-facing owner: `associatedPrimesOfModule R M`;
- filtration owner: `s.primeFactors`;
- canonical Noetherian owner: mathlib's `associatedPrimes R M`;
- layer of this file: `bridge/view`, first from associated-prime points to the intrinsic filtration
  owner `s.primeFactors`, then from that owner statement to a chosen indexing `p`.
-/

/-- Owner-form companion to Lemma 10.63.4: the associated prime points of `M` lie among the prime
factors occurring in the given prime-cyclic filtration. -/
theorem associatedPrimePointsOfModule_subset_primeFactors_of_prime_quotient_filtration
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤)
    :
    asIdeal ⁻¹' associatedPrimesOfModule R M ⊆
      s.primeFactors := sorry

variable (p : Fin s.length → PrimeSpectrum R)

/-- Lemma 10.63.4: if `M` admits a finite filtration by submodules whose successive quotients are
isomorphic to quotients `R ⧸ p i` by prime ideals, then every textbook-associated prime of `M`
comes from one of the prime points occurring in that filtration. This ideal-valued form is the
image of the prime-spectrum owner statement under `PrimeSpectrum.asIdeal`. -/
-- Proof sketch: induct on the length of the relation series. For the last step, apply
-- the source-facing associated-prime description to the last short exact sequence
-- `0 → s.eraseLast.last → s.last → quotient → 0`; identify the associated primes of the quotient
-- with the singleton `{(p i).asIdeal}` using the chosen quotient isomorphism and the cyclic
-- description of
-- `Ass(R ⧸ p)`, then use the induction hypothesis on the truncated filtration.
theorem associatedPrimesOfModule_subset_range_of_prime_quotient_filtration
    (hp : ∀ i,
      Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ (p i).asIdeal))
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤)
    : associatedPrimesOfModule R M ⊆ asIdeal '' Set.range p := by
  have hsubset :
      asIdeal ⁻¹' associatedPrimesOfModule R M ⊆ Set.range p := by
    simpa [s.primeFactors_eq_range p hp] using
      associatedPrimePointsOfModule_subset_primeFactors_of_prime_quotient_filtration s hs₀ hs_top
  intro I hI
  have hpoint :
      (⟨I, hI.1⟩ : PrimeSpectrum R) ∈ asIdeal ⁻¹' associatedPrimesOfModule R M := by
    simpa
  rcases hsubset hpoint with ⟨i, hi⟩
  refine ⟨p i, ⟨⟨i, rfl⟩, ?_⟩⟩
  exact congrArg asIdeal hi

/-- In the Noetherian setting, Lemma 10.63.4 can be restated using the canonical mathlib set
`associatedPrimes R M`. -/
theorem associatedPrimes_subset_range_of_prime_quotient_filtration [IsNoetherianRing R]
    (hp : ∀ i,
      Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ (p i).asIdeal))
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤)
    : associatedPrimes R M ⊆ asIdeal '' Set.range p := by
  simpa [associatedPrimesOfModule_eq_associatedPrimes R M] using
    associatedPrimesOfModule_subset_range_of_prime_quotient_filtration s p hp hs₀ hs_top

end
