import stacks_proof.stacks_project.Chap10.Lemma_10_62_2
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum

section SupportAndDimensionOfModules

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

variable (s : PrimeCyclicFiltration R M)

-- Proof sketch: use Lemma 10.62.2 to identify `Module.support R M` with the union of the zero
-- loci of the prime ideals appearing as successive prime-quotient factors of `s`. A prime point is
-- minimal in that union exactly when it is minimal among those prime factors.
/-- Lemma 10.62.5: a prime point of `Spec R` is minimal among the prime factors occurring in a
finite prime-cyclic filtration of `M` from `0` to `M` if and only if it is a minimal element of
`Module.support R M`. -/
@[stacks 00L7]
theorem minimal_primeFactor_iff_minimal_support_of_prime_cyclic_filtration
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤)
    (𝔭 : PrimeSpectrum R) :
    Minimal (· ∈ s.primeFactors) 𝔭 ↔
      Minimal (· ∈ Module.support R M) 𝔭 := by
  have hsupport :=
    support_eq_iUnion_zeroLocus_of_prime_cyclic_filtration s hs₀ hs_top
  have hprimeFactors :=
    primeFactors_subset_support_of_prime_cyclic_filtration s hs₀ hs_top
  constructor
  · intro h𝔭
    refine ⟨hprimeFactors h𝔭.1, ?_⟩
    intro q hq hq𝔭
    rw [hsupport] at hq
    rcases Set.mem_iUnion.1 hq with ⟨r, hrq⟩
    have hrq' : r.1 ≤ q := by
      simpa using (mem_zeroLocus q (r.1.asIdeal : Set R)).1 hrq
    exact (h𝔭.2 r.2 (hrq'.trans hq𝔭)).trans hrq'
  · intro h𝔭
    have h𝔭_support : 𝔭 ∈ Module.support R M := h𝔭.1
    rw [hsupport] at h𝔭_support
    rcases Set.mem_iUnion.1 h𝔭_support with ⟨r, hr𝔭⟩
    have hr𝔭' : r.1 ≤ 𝔭 := by
      simpa using (mem_zeroLocus 𝔭 (r.1.asIdeal : Set R)).1 hr𝔭
    have h𝔭r : 𝔭 ≤ r.1 := h𝔭.2
      (hprimeFactors r.2) hr𝔭'
    have h𝔭_eq : 𝔭 = r.1 := le_antisymm h𝔭r hr𝔭'
    refine ⟨h𝔭_eq ▸ r.2, ?_⟩
    intro q hq hq𝔭
    exact h𝔭.2 (hprimeFactors hq) hq𝔭

end SupportAndDimensionOfModules
