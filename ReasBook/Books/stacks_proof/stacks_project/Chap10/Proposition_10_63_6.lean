import Mathlib.Data.List.TFAE
import stacks_proof.stacks_project.Chap10.Lemma_10_62_5
import stacks_proof.stacks_project.Chap10.Lemma_10_63_2
import stacks_proof.stacks_project.Chap10.Lemma_10_63_8
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum Module.associatedPrimes

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Proposition 10.63.6: for a finite module over a Noetherian ring, a prime point `𝔭 : Spec R`
is minimal in the support of `M` if and only if its underlying ideal is minimal among the
associated primes of `M`. -/
-- Proof sketch: the inclusion `Ass(M) ⊆ Supp(M)` is Lemma `10.63.2`. Conversely, a minimal point
-- of the support is associated by the minimal-support criterion from this section. Minimality then
-- upgrades these inclusions to an equivalence on minimal primes.
@[stacks 02CE]
theorem minimal_support_iff_minimal_associatedPrimes
    (𝔭 : PrimeSpectrum R) :
    Minimal (· ∈ Module.support R M) 𝔭 ↔
      Minimal (· ∈ associatedPrimes R M) 𝔭.asIdeal := by
  constructor
  · intro h𝔭
    refine ⟨Module.minimal_support_mem_associatedPrimes 𝔭 h𝔭, ?_⟩
    intro q hq hq𝔭
    let q' : PrimeSpectrum R := ⟨q, hq.1⟩
    have hq' : q' ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M := by
      simpa [q'] using hq
    exact h𝔭.2 (Module.associatedPrimes_subset_support hq') hq𝔭
  · intro h𝔭
    have h𝔭' : 𝔭 ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M := by
      simpa using h𝔭.1
    refine ⟨Module.associatedPrimes_subset_support h𝔭', ?_⟩
    intro q hq hq𝔭
    obtain ⟨r, hr, hrq⟩ := Ideal.exists_minimalPrimes_le (Module.mem_support_iff_of_finite.mp hq)
    let r' : PrimeSpectrum R := ⟨r, hr.1.1⟩
    have hr_assoc : r ∈ associatedPrimes R M :=
      minimalPrimes_annihilator_subset_associatedPrimes R M hr
    have h𝔭r : 𝔭.asIdeal ≤ r := h𝔭.2 hr_assoc (hrq.trans hq𝔭)
    exact h𝔭r.trans hrq

omit [IsNoetherianRing R] [Module.Finite R M] in
private theorem minimal_associatedPrimePoints_iff_minimal_associatedPrimes
    (𝔭 : PrimeSpectrum R) :
    Minimal (· ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M) 𝔭 ↔
      Minimal (· ∈ associatedPrimes R M) 𝔭.asIdeal := by
  constructor
  · intro h𝔭
    refine ⟨by simpa using h𝔭.1, ?_⟩
    intro q hq hq𝔭
    let q' : PrimeSpectrum R := ⟨q, hq.1⟩
    have hq' : q' ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M := by
      simpa [q'] using hq
    exact h𝔭.2 hq' hq𝔭
  · intro h𝔭
    refine ⟨by simpa using h𝔭.1, ?_⟩
    intro q hq hq𝔭
    exact h𝔭.2 hq (show q.asIdeal ≤ 𝔭.asIdeal from hq𝔭)

/- Proposition 10.63.6 also identifies minimal support points with the minimal prime factors of any
prime cyclic filtration. The prime-spectrum associated-prime condition needed for the three-way TFAE
is a bridge/view of the owner theorem `minimal_support_iff_minimal_associatedPrimes`, while the
filtration comparison is exactly the owner theorem
`minimal_primeFactor_iff_minimal_support_of_prime_cyclic_filtration` from Lemma `10.62.5`. -/

/-- Proposition 10.63.6, reformulated as the equivalence of the three textbook conditions at a
fixed prime point of `Spec R`. -/
@[stacks 02CE]
theorem minimal_support_associatedPrimes_prime_quotient_filtration_tfae
    (s : PrimeCyclicFiltration R M) (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤) (𝔭 : PrimeSpectrum R) :
    List.TFAE
      [ Minimal (· ∈ Module.support R M) 𝔭,
        Minimal (· ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M) 𝔭,
        Minimal (· ∈ s.primeFactors) 𝔭 ] := by
  tfae_have 1 ↔ 2 := by
    rw [minimal_support_iff_minimal_associatedPrimes, ←
      minimal_associatedPrimePoints_iff_minimal_associatedPrimes 𝔭]
  tfae_have 1 ↔ 3 :=
    (minimal_primeFactor_iff_minimal_support_of_prime_cyclic_filtration s hs₀ hs_top 𝔭).symm
  tfae_finish

end
