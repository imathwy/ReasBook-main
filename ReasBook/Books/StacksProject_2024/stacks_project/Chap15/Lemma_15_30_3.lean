import Mathlib
import StacksProject_2024.Chap15.Definition_15_30_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Proof sketch: unfold `IsKoszulRegularOn`; specializing the defining vanishing statement to
-- degree `1` gives exactly `IsH1RegularOn`.
/-- Lemma 15.30.3 (1): an `M`-Koszul-regular finite family is `M`-`H_1`-regular. -/
theorem isH1RegularOn_of_isKoszulRegularOn {r : ℕ} {f : Fin r → R}
    (hKoszul : IsKoszulRegularOn M f) : IsH1RegularOn M f := by
  simpa [IsKoszulRegularOn, IsH1RegularOn] using hKoszul 1 le_rfl

-- Proof sketch: specialize `isH1RegularOn_of_isKoszulRegularOn` to the regular module `R`.
/-- Lemma 15.30.3 (2): a Koszul-regular finite family is `H_1`-regular. -/
theorem isH1RegularSequence_of_isKoszulRegularSequence {r : ℕ} {f : Fin r → R}
    (hKoszul : IsKoszulRegularSequence f) : IsH1RegularSequence f :=
  isH1RegularOn_of_isKoszulRegularOn hKoszul

end RingTheory.Sequence
