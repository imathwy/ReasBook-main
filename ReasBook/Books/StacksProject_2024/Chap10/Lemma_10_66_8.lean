import Mathlib
import StacksProject_2024.Chap10.Lemma_10_66_2
import StacksProject_2024.Chap10.Lemma_10_66_5
import StacksProject_2024.Chap10.Lemma_10_66_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum Localization

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
* primary domain: commutative algebra of module support, localization at a prime, and weakly
  associated primes;
* sampled owner abstractions: `Module.support`, `Module.support_subset_preimage_comap`,
  `weaklyAssociatedPrimes`, and
  `isWeaklyAssociatedToModule_iff_isWeaklyAssociatedToModule_maximalIdeal_atPrime`;
* layer: `bridge/view`, since the target theorem translates a minimal-support point into membership
  in the owner set `weaklyAssociatedPrimes R M`.

Primitive data are only the original module, its prime localization, and the canonical owner sets.
The local support-descent helper below remains private because the sampled upstream support API does
not provide this exact `IsLocalizedModule` descent statement. -/

private theorem mem_support_comap_of_mem_support_of_isLocalizedModule
    (S : Submonoid R) {R' : Type*} [CommRing R'] [Algebra R R']
    {M' : Type*} [AddCommGroup M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] {q : PrimeSpectrum R'}
    (hq : q ∈ Module.support R' M') :
    PrimeSpectrum.comap (algebraMap R R') q ∈ Module.support R M := by
  rw [Module.mem_support_iff_exists_annihilator] at hq ⊢
  obtain ⟨x, hx⟩ := hq
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
  refine ⟨m, fun r hr ↦ ?_⟩
  rw [Submodule.mem_annihilator_span_singleton] at hr
  exact hx <| by
    rw [Submodule.mem_annihilator_span_singleton]
    simpa [algebraMap_smul] using
      (show r • IsLocalizedModule.mk' f m s = 0 by
        rw [← IsLocalizedModule.mk'_smul, hr, IsLocalizedModule.mk'_zero])

/-- Lemma 10.66.8: if a prime point `𝔭` is minimal in the support of an `R`-module `M`, then its
underlying ideal is a weakly associated prime of `M`. -/
-- Proof sketch: localize at `𝔭`. Minimality in the support forces the support of the localized
-- module to be the singleton closed point, so the localization is nonzero. Lemma 10.66.5 then
-- gives a weakly associated prime of the localized module; Lemma 10.66.6 shows it must be the
-- maximal ideal of the localization, and Lemma 10.66.2 descends this weak association back to
-- `M`.
theorem minimal_support_mem_weaklyAssociatedPrimes
    (𝔭 : PrimeSpectrum R)
    (h𝔭 : Minimal (· ∈ Module.support R M) 𝔭) :
    𝔭.asIdeal ∈ weaklyAssociatedPrimes R M := by
  let Rₚ := Localization.AtPrime 𝔭.asIdeal
  let Mₚ := LocalizedModule.AtPrime 𝔭.asIdeal M
  haveI : Nontrivial Mₚ := Module.mem_support_iff.mp h𝔭.1
  obtain ⟨q, hq⟩ : (weaklyAssociatedPrimes Rₚ Mₚ).Nonempty := weaklyAssociatedPrimes.nonempty
  let q' : PrimeSpectrum Rₚ := ⟨q, hq.isPrime⟩
  have hq_support : q' ∈ Module.support Rₚ Mₚ := by
    simpa [q'] using hq.mem_support
  have hq_comap_support : PrimeSpectrum.comap (algebraMap R Rₚ) q' ∈ Module.support R M := by
    exact
      mem_support_comap_of_mem_support_of_isLocalizedModule
        𝔭.asIdeal.primeCompl (LocalizedModule.mkLinearMap 𝔭.asIdeal.primeCompl M) hq_support
  have hq_comap_le : PrimeSpectrum.comap (algebraMap R Rₚ) q' ≤ 𝔭 := by
    change ((IsLocalization.AtPrime.primeSpectrumOrderIso Rₚ 𝔭.asIdeal q').1 ≤ 𝔭)
    exact (IsLocalization.AtPrime.primeSpectrumOrderIso Rₚ 𝔭.asIdeal q').2
  have hq_comap_eq : Ideal.comap (algebraMap R Rₚ) q = 𝔭.asIdeal := by
    have : PrimeSpectrum.comap (algebraMap R Rₚ) q' = 𝔭 :=
      le_antisymm hq_comap_le (h𝔭.2 hq_comap_support hq_comap_le)
    simpa [PrimeSpectrum.comap_asIdeal, q'] using congrArg PrimeSpectrum.asIdeal this
  have hq_eq : q = IsLocalRing.maximalIdeal Rₚ := by
    exact AtPrime.eq_maximalIdeal_iff_comap_eq.mp hq_comap_eq
  exact
    (isWeaklyAssociatedToModule_iff_isWeaklyAssociatedToModule_maximalIdeal_atPrime
      𝔭.asIdeal).2 <|
      hq_eq ▸ hq

end
