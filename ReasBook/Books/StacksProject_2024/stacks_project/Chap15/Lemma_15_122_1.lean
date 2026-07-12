import Mathlib
import StacksProject_2024.Chap15.Lemma_15_118_3
import StacksProject_2024.Chap15.Lemma_15_122_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/-- Lemma 15.122.1: if `R` is a regular local ring and `f ∈ R`, then the localization `R_f`,
realized as `Localization.Away f`, has trivial Picard group. -/
theorem subsingleton_picardGroup_localizationAway_of_isRegularLocalRing
    {R : Type u} [CommRing R] [IsRegularLocalRing R] (f : R) :
    Subsingleton (CommRing.Pic (Localization.Away f)) := by
  -- A regular local ring is factorial by Lemma `15.122.2`, and localizations of factorial
  -- domains remain factorial. The Picard group of a factorial domain is trivial by
  -- Lemma `15.118.3`.
  simpa using
    (subsingleton_picardGroup_of_uniqueFactorizationMonoid (R := Localization.Away f))

end
