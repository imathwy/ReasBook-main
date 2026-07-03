import StacksProject_2024.Chap15.Lemma_15_29_1
import StacksProject_2024.Chap15.Definition_15_30_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory.Limits

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

-- Proof sketch: by Lemma 15.30.4 and induction, replacing any entry of a Koszul-regular sequence
-- by a positive power preserves Koszul-regularity, and Lemma 15.28.4 lets us permute the sequence.
-- Hence each powered family `(fun i ↦ f i ^ (n + 1))` is still Koszul-regular, so its Koszul
-- complex has vanishing positive homology. Lemma 15.29.6 identifies the extended alternating Čech
-- complex with the colimit of these Koszul complexes, from which the only possible nonvanishing
-- cohomology degree is the top degree `r`.
/-- Lemma 15.31.1: if `f : Fin r → R` is a Koszul-regular sequence, then the extended alternating
Čech complex attached to `f` has vanishing cohomology in every degree `i ≠ r`. -/
theorem extendedAlternatingCechComplex_homology_isZero_of_isKoszulRegularSequence {r : ℕ}
    (f : Fin r → R) (hKoszul : IsKoszulRegularSequence f) (i : ℕ) (hi : i ≠ r) :
    IsZero ((extendedAlternatingCechComplex f R).homology i) := sorry

end RingTheory.Sequence
