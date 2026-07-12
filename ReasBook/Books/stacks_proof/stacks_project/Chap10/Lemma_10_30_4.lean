import StacksProject_2024.Chap10.Lemma_10_30_6
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [IsDomain R] [CommRing S]

/-- Lemma 10.30.4: for a ring map `φ : R →+* S` with `R` a domain, the following are equivalent:
`φ` is injective, `Spec S → Spec R` has dense range, and the generic point `(0)` of `Spec R`
lies in the image. This is the domain specialization of the general dense-range TFAE in
`Lemma_10_30_6`, using that a domain has nilradical `0` and a unique minimal point `(0)`. -/
@[stacks 00FJ]
theorem ringHom_injective_tfae_of_image_contains_dense_set
    (φ : R →+* S) :
    List.TFAE
      [ Function.Injective φ,
        DenseRange (comap φ),
        (⊥ : PrimeSpectrum R) ∈ Set.range (comap φ) ] := by
  have howner := denseRange_comap_tfae_ker_le_nilradical_minimalPrimes φ
  have hinjective : Function.Injective φ ↔ RingHom.ker φ ≤ nilradical R := by
    rw [RingHom.injective_iff_ker_eq_bot]
    simp [le_bot_iff]
  have hminimal :
      (∀ p : PrimeSpectrum R, IsMin p → p ∈ Set.range (comap φ)) ↔
        (⊥ : PrimeSpectrum R) ∈ Set.range (comap φ) := by
    constructor
    · intro h
      exact h ⊥ <| by
        rw [isMin_iff]
        simp [IsDomain.minimalPrimes_eq_singleton_bot R]
    · intro h p hp
      have hp_bot : p = ⊥ := by
        rw [isMin_iff] at hp
        apply PrimeSpectrum.ext
        simpa [IsDomain.minimalPrimes_eq_singleton_bot R] using hp
      simpa [hp_bot] using h
  tfae_have 1 ↔ 2 := by
    exact hinjective.trans (howner.out 0 2)
  tfae_have 2 ↔ 3 := by
    exact (howner.out 2 1).trans hminimal
  tfae_finish

end
