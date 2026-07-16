import Mathlib
import StacksProject_2024.stacks_project.Chap23.Lemma_23_8_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-
Semantic recall note: `lean_leansearch` only surfaced general localization criteria for properties
detected on maximal localizations, so the owner choice here follows the verified chapter owners
`IsCompleteIntersectionLocalRing`, `IsLocalCompleteIntersectionRing`, and the prime-local descent
statement `isCompleteIntersectionLocalRing_localizationAtPrime`.
-/

/-- Lemma 23.8.7: let `A` be a Noetherian ring. Then `A` is a local complete intersection if and
only if `A_𝔪` is a complete intersection for every maximal ideal `𝔪` of `A`. -/
@[stacks 09Q5]
theorem isLocalCompleteIntersectionRing_iff_forall_maximal_isCompleteIntersectionLocalRing :
    IsLocalCompleteIntersectionRing A ↔
      ∀ m : MaximalSpectrum A,
        IsCompleteIntersectionLocalRing (Localization.AtPrime m.asIdeal) := sorry

end
