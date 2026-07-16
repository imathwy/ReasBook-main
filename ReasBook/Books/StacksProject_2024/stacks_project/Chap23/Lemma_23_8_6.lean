import Mathlib
import StacksProject_2024.stacks_project.Chap23.Definition_23_8_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A] [IsCompleteIntersectionLocalRing A]

/-
Semantic recall note: `lean_leansearch` only surfaced the standard prime-localization
infrastructure, so the owner choice here follows the verified chapter owner
`IsCompleteIntersectionLocalRing`, its primewise ring-level companion
`IsLocalCompleteIntersectionRing`, and the local analogue
`isRegularLocalRing_localizationAtPrime`.
-/

/-- Lemma 23.8.6: let `(A, 𝔪)` be a Noetherian local ring and let `𝔭 ⊂ A` be a prime ideal. If
`A` is a complete intersection, then the local ring `A_𝔭` is a complete intersection too. -/
@[stacks 09Q4]
theorem isCompleteIntersectionLocalRing_localizationAtPrime (p : PrimeSpectrum A) :
    IsCompleteIntersectionLocalRing (Localization.AtPrime p.asIdeal) := sorry

end
