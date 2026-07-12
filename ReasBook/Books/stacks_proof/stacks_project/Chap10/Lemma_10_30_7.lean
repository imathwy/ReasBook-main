import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.30.7: if a minimal point `p` of `Spec R` lies in the image of `Spec S → Spec R`,
then it is the image of a minimal point of `Spec S`. By `isMin_iff`, this is
equivalent to the source statement about minimal prime ideals. -/
-- Proof sketch: the image hypothesis shows `ker f ≤ p.asIdeal`, so `p.asIdeal` is a minimal
-- prime over `ker f`. The owner lemma `Ideal.exists_minimalPrimes_comap_eq` then produces a
-- minimal prime `q'` of `S` with `comap f q' = p`.
@[stacks 0CAN]
theorem exists_isMin_comap_eq_of_mem_range_comap (f : R →+* S) (p : PrimeSpectrum R)
    (hp : IsMin p) (hp_range : p ∈ Set.range (comap f)) :
    ∃ q : PrimeSpectrum S, IsMin q ∧ comap f q = p := by
  rcases hp_range with ⟨q, hq⟩
  have hp' : p.asIdeal ∈ (RingHom.ker f).minimalPrimes := by
    refine ⟨⟨p.2, ?_⟩, ?_⟩
    · rw [← hq]
      exact Ideal.ker_le_comap f
    intro I hI hIp
    exact (isMin_iff.mp hp).2 ⟨hI.1, bot_le⟩ hIp
  obtain ⟨q', hq', hq'eq⟩ := Ideal.exists_minimalPrimes_comap_eq f p.asIdeal hp'
  exact ⟨⟨q', Ideal.minimalPrimes_isPrime hq'⟩, isMin_iff.mpr hq', PrimeSpectrum.ext hq'eq⟩

end
