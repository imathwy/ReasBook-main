import Mathlib
import StacksProject_2024.Chap10.Definition_10_70_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum

section

variable {R : Type u} [CommRing R]

/-- Lemma 10.70.11: if `a ∈ I` and `a` is contained in no minimal prime of `R`, then the induced
map `Spec(R[I/a]) → Spec(R)` has dense image. -/
-- Proof sketch: the owner abstraction for density is `DenseRange (comap f)`, equivalently the
-- condition that every minimal prime lies in the image. If `a ∉ p` for a minimal prime `p`, then
-- `p` lies in the image of `Spec(R_a) → Spec(R)` because that image is the basic open `D(a)`.
-- Composing with the canonical comparison map `R[I/a] → R_a` lifts this image point to
-- `Spec(R[I/a])`, so every minimal prime of `R` lies in the image of `Spec(R[I/a]) → Spec(R)`.
theorem denseRange_comap_affineBlowupChart_of_not_mem_minimalPrimes
    (I : Ideal R) (a : I) (hmin : ∀ p ∈ minimalPrimes R, (a : R) ∉ p) :
    DenseRange (comap (algebraMap R (affineBlowupChart I a))) := by
  rw [denseRange_comap_iff_minimalPrimes]
  intro p hp
  let p' : PrimeSpectrum R := ⟨p, Ideal.minimalPrimes_isPrime hp⟩
  have hp_range : p' ∈ Set.range (comap (algebraMap R (Localization.Away (a : R)))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (a : R)) (a : R)]
    exact (PrimeSpectrum.mem_basicOpen (a : R) p').2 (hmin p hp)
  rcases hp_range with ⟨q, hq⟩
  refine ⟨PrimeSpectrum.comap (affineBlowupChartToLocalizationAway I a) q, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply,
    affineBlowupChartToLocalizationAway_comp_algebraMap]
  exact hq

end
