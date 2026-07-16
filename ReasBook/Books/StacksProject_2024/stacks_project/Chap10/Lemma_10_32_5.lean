import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_32_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommSemiring R] [IsNoetherianRing R]

namespace Ideal

/-- Lemma 10.32.5 (1): in a Noetherian ring, the owner theorem
`Ideal.exists_pow_le_of_le_radical_of_fg` applies to every ideal. -/
theorem exists_pow_le_of_le_radical_of_isNoetherianRing {I J : Ideal R} (hJI : J ≤ I.radical) :
    ∃ n : ℕ, J ^ n ≤ I :=
  exists_pow_le_of_le_radical_of_fg hJI J.fg_of_isNoetherianRing

/-- Lemma 10.32.5 (2), textbook wording: in a Noetherian ring, each element of an ideal is
nilpotent if and only if the ideal itself is nilpotent. This is the source-facing bridge from the
chapter notion `I.IsLocallyNilpotent` to the owner theorem `FG.isNilpotent_iff_le_nilradical`. -/
theorem forall_mem_isNilpotent_iff_isNilpotent (I : Ideal R) :
    (∀ x ∈ I, IsNilpotent x) ↔ IsNilpotent I := by
  rw [← isLocallyNilpotent_iff I]
  simpa [IsLocallyNilpotent] using
    (FG.isNilpotent_iff_le_nilradical I.fg_of_isNoetherianRing).symm

end Ideal

end
