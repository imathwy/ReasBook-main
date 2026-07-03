import Mathlib
import stacks_project.Chap10.Lemma_10_66_7
import stacks_project.Chap10.Lemma_10_66_15

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open weaklyAssociatedPrimes

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (S : Submonoid R)

local notation "Mₛ" => LocalizedModule S M

/- Domain triage:
* `core/canonical`: the owner abstraction is the set-valued declaration
  `weaklyAssociatedPrimes R M`.
* `bridge/view`: Lemma 10.66.15 provides the localization comparison
  `weaklyAssociatedPrimes.inter_eq_localizedModule`.
* This file is derived owner API: the regularity hypothesis forces every weakly associated prime
  of `M` to be disjoint from `S`, so the bridge theorem specializes to equality. -/

/-- Lemma 10.66.16: if every element of the multiplicative subset `S` acts on `M` by a
nonzerodivisor, then the weakly associated primes of `M` coincide with those of the localized
module `LocalizedModule S M`, viewed as an `R`-module. -/
-- Proof sketch: the hypothesis implies that the localization map `M → LocalizedModule S M` is
-- injective, so Lemma 10.66.4 gives `WeakAss(M) ⊆ WeakAss(S⁻¹M)`. Conversely, if `n / s` in the
-- localization has annihilator with minimal prime `𝔭`, then the same ideal annihilates `n : M`,
-- so `𝔭` is already weakly associated to `M`.
theorem weaklyAssociatedPrimes_eq_localizedModule
    (hS : ∀ s : S, IsSMulRegular M s) :
    weaklyAssociatedPrimes R M = weaklyAssociatedPrimes R Mₛ := by
  have hdisjoint :
      weaklyAssociatedPrimes R M ⊆ {𝔭 : Ideal R | Disjoint (S : Set R) (𝔭 : Set R)} := by
    intro 𝔭 h𝔭
    change Disjoint (S : Set R) (𝔭 : Set R)
    rw [Set.disjoint_left]
    intro s hsS hs𝔭
    have hs_not_mem : (s : R) ∉ ⋃ 𝔮 ∈ weaklyAssociatedPrimes R M, 𝔮 := by
      rw [weaklyAssociatedPrimes.biUnion_eq_compl_regular, Set.mem_compl_iff, Set.mem_setOf_eq]
      exact not_not_intro <| hS ⟨s, hsS⟩
    exact hs_not_mem <| Set.mem_iUnion.2 ⟨𝔭, Set.mem_iUnion.2 ⟨h𝔭, hs𝔭⟩⟩
  have hlocal :
      weaklyAssociatedPrimes R M ∩ {𝔭 : Ideal R | Disjoint (S : Set R) (𝔭 : Set R)} =
        weaklyAssociatedPrimes R Mₛ :=
    inter_eq_localizedModule S
  simpa [Set.inter_eq_left.2 hdisjoint] using hlocal

end
