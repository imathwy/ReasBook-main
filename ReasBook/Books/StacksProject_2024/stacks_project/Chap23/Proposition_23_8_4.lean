import Mathlib
import StacksProject_2024.Chap23.Definition_23_8_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]

/-
Semantic recall note: `lean_leansearch` surfaced `AdicCompletion.flat_of_isNoetherian` and
`Module.FaithfullyFlat.of_flat_of_isLocalHom`; together with the verified local owner
`IsCompleteIntersectionLocalRing`, this supports phrasing the textbook completion criterion on the
canonical local-ring owner and writing the closed fiber via the explicit quotient
`B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)`.
-/

/-- Proposition 23.8.4: let `A → B` be a flat local homomorphism of Noetherian local rings. Then
the following are equivalent: the maximal-ideal completion `B^∧` is a complete intersection; the
maximal-ideal completion `A^∧` is a complete intersection and the completion of the closed fiber
`B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)`, i.e. `(B / 𝔪_A B)^∧`, is a complete
intersection. -/
@[stacks 09Q2]
theorem isCompleteIntersectionLocalRing_iff_source_and_closedFiber_of_flat_localHom :
    IsCompleteIntersectionLocalRing B ↔
      IsCompleteIntersectionLocalRing A ∧
        IsCompleteIntersectionLocalRing (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) := sorry

end
