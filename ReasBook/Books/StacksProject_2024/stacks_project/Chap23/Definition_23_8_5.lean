import Mathlib.RingTheory.AdicCompletion.Algebra
import StacksProject_2024.Chap23.CompleteIntersectionCompleteLocalRing

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R]

/-- Definition 23.8.5 (1): a Noetherian local ring is a complete intersection if its maximal-ideal
adic completion is a complete intersection complete local ring. -/
@[stacks 09Q3 "(1)"]
class IsCompleteIntersectionLocalRing (R : Type u) [CommRing R] : Prop extends
    IsLocalRing R, IsNoetherianRing R where
  completion_isCompleteIntersection :
    IsCompleteIntersectionCompleteLocalRing (AdicCompletion (maximalIdeal R) R)

/-- Unfold Definition 23.8.5 (1) into the Noetherian hypothesis and the completion condition. -/
theorem isCompleteIntersectionLocalRing_iff (R : Type u) [CommRing R] [IsLocalRing R] :
    IsCompleteIntersectionLocalRing R ↔
      IsNoetherianRing R ∧
        IsCompleteIntersectionCompleteLocalRing (AdicCompletion (maximalIdeal R) R) := by
  constructor
  · intro h
    letI : IsCompleteIntersectionLocalRing R := h
    exact ⟨inferInstance, h.completion_isCompleteIntersection⟩
  · rintro ⟨hNoetherian, hCompletion⟩
    letI : IsNoetherianRing R := hNoetherian
    exact { completion_isCompleteIntersection := hCompletion }

attribute [instance] IsCompleteIntersectionLocalRing.completion_isCompleteIntersection

namespace IsCompleteIntersectionLocalRing

/-- A Noetherian local ring is a complete intersection once its maximal-ideal completion is a
complete-intersection complete local ring. -/
theorem of_completion
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hCompletion :
      IsCompleteIntersectionCompleteLocalRing (AdicCompletion (maximalIdeal R) R)) :
    IsCompleteIntersectionLocalRing R := by
  exact (isCompleteIntersectionLocalRing_iff R).2 ⟨inferInstance, hCompletion⟩

end IsCompleteIntersectionLocalRing

/-- Definition 23.8.5 (2): a Noetherian ring is a local complete intersection if all of its local
rings are complete intersections. -/
@[stacks 09Q3 "(2)"]
class IsLocalCompleteIntersectionRing (R : Type u) [CommRing R] : Prop extends
    IsNoetherianRing R where
  completeIntersection_atPrime :
    ∀ p : PrimeSpectrum R, IsCompleteIntersectionLocalRing (Localization.AtPrime p.asIdeal)

/-- Unfold Definition 23.8.5 (2) into the Noetherian hypothesis and the primewise local-ring
criterion. -/
theorem isLocalCompleteIntersectionRing_iff (R : Type u) [CommRing R] :
    IsLocalCompleteIntersectionRing R ↔
      IsNoetherianRing R ∧
        ∀ p : PrimeSpectrum R,
          IsCompleteIntersectionLocalRing (Localization.AtPrime p.asIdeal) := by
  constructor
  · intro h
    letI : IsLocalCompleteIntersectionRing R := h
    exact ⟨inferInstance, h.completeIntersection_atPrime⟩
  · rintro ⟨hNoetherian, hPrime⟩
    letI : IsNoetherianRing R := hNoetherian
    exact { completeIntersection_atPrime := hPrime }

attribute [instance] IsLocalCompleteIntersectionRing.completeIntersection_atPrime

namespace IsLocalCompleteIntersectionRing

/-- A Noetherian ring is a local complete intersection once all of its localizations at primes are
complete intersections. -/
theorem of_localizationAtPrime
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hPrime :
      ∀ p : PrimeSpectrum R, IsCompleteIntersectionLocalRing (Localization.AtPrime p.asIdeal)) :
    IsLocalCompleteIntersectionRing R := by
  exact (isLocalCompleteIntersectionRing_iff R).2 ⟨inferInstance, hPrime⟩

end IsLocalCompleteIntersectionRing

end
