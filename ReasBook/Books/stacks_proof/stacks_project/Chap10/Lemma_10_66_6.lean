import stacks_proof.stacks_project.Chap10.Definition_10_63_1
import stacks_proof.stacks_project.Chap10.Definition_10_66_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

theorem IsAssociatedPrime.isWeaklyAssociatedToModule {𝔭 : Ideal R}
    (h𝔭 : IsAssociatedPrime 𝔭 M) :
    Ideal.IsWeaklyAssociatedToModule R M 𝔭 := by
  rcases h𝔭.eq_radical_colon with ⟨m, hm⟩
  have htorsion : Ideal.torsionOf R M m = (⊥ : Submodule R M).colon ({m} : Set M) := by
    calc
      Ideal.torsionOf R M m = (Submodule.span R ({m} : Set M)).annihilator := by
        simpa [Ideal.torsionOf] using (Submodule.annihilator_span_singleton m).symm
      _ = (⊥ : Submodule R M).colon ({m} : Set M) := by
        rw [Submodule.bot_colon']
  have hp : (Ideal.torsionOf R M m).radical.IsPrime := by
    simpa [htorsion, hm] using h𝔭.isPrime
  letI := hp
  refine ⟨m, ?_⟩
  rw [← Ideal.radical_minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self]
  simp [htorsion, hm]

namespace Ideal

/-- Source-facing pointwise form of the first inclusion in Lemma 10.66.6. -/
theorem IsAssociatedToModule.isWeaklyAssociatedToModule {𝔭 : Ideal R}
    (h𝔭 : IsAssociatedToModule R M 𝔭) :
    IsWeaklyAssociatedToModule R M 𝔭 := by
  exact h𝔭.isAssociatedPrime.isWeaklyAssociatedToModule

end Ideal

namespace Ideal

/-- Canonical pointwise form of the second inclusion in Lemma 10.66.6. -/
theorem IsWeaklyAssociatedToModule.mem_support {𝔭 : Ideal R}
    (h𝔭 : Ideal.IsWeaklyAssociatedToModule R M 𝔭) :
    (⟨𝔭, h𝔭.isPrime⟩ : PrimeSpectrum R) ∈ Module.support R M := by
  rcases h𝔭 with ⟨m, hm⟩
  rw [Module.mem_support_iff_exists_annihilator]
  exact ⟨m, by simpa [Ideal.torsionOf, Submodule.annihilator_span_singleton] using hm.1.2⟩

end Ideal

namespace associatedPrimesOfModule

/-- Lemma 10.66.6 (1): every textbook-associated prime of `M` is weakly associated to `M`. -/
@[stacks 0589]
theorem subset_weaklyAssociatedPrimes :
    associatedPrimesOfModule R M ⊆ weaklyAssociatedPrimes R M := by
  intro 𝔭 h𝔭
  exact (associatedPrimesOfModule_subset_associatedPrimes R M h𝔭).isWeaklyAssociatedToModule

end associatedPrimesOfModule

namespace associatedPrimes

/-- Lemma 10.66.6 (2): every associated prime of `M` is weakly associated to `M`. -/
@[stacks 0589]
theorem subset_weaklyAssociatedPrimes :
    associatedPrimes R M ⊆ weaklyAssociatedPrimes R M := by
  intro 𝔭 h𝔭
  exact (AssociatedPrimes.mem_iff.mp h𝔭).isWeaklyAssociatedToModule

end associatedPrimes

namespace weaklyAssociatedPrimes

/-- Lemma 10.66.6 (3): a weakly associated prime of `M`, viewed as a point of `Spec R`, lies in the
support of `M`. -/
@[stacks 0589]
theorem subset_support :
    PrimeSpectrum.asIdeal ⁻¹' weaklyAssociatedPrimes R M ⊆ Module.support R M := by
  intro 𝔭 h𝔭
  simpa using (show Ideal.IsWeaklyAssociatedToModule R M 𝔭.asIdeal from h𝔭).mem_support

end weaklyAssociatedPrimes

end
