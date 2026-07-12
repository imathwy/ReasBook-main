import Mathlib
import StacksProject_2024.Chap10.Lemma_10_97_7
import StacksProject_2024.Chap15.Definition_15_33_2
import StacksProject_2024.Chap15.Definition_15_61_1
import StacksProject_2024.Chap23.Definition_23_8_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing

section

variable {A B : Type u}
variable [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]

/- Semantic search note: `lean_leansearch` did not return useful local-complete-intersection hits
for this item, so the owner choice was checked directly against the local Chapter 23/15 API
`IsCompleteIntersectionLocalRing`, `RingHom.IsLocalCompleteIntersection`, and
`maximalIdealCompletionMap`. -/

/-- Proposition 23.9.2 (1): if `B` is a complete intersection and `Tor_p^A(B, A / 𝔪_A)` is
nonzero for only finitely many `p`, then `A` is a complete intersection and the induced map on
maximal-ideal completions `A^∧ → B^∧` is a local complete intersection homomorphism. -/
@[stacks 09QB]
theorem sourceCompleteIntersection_completionMapLocalCompleteIntersection_of_targetCompleteIntersection_torVanishing
    (hB : IsCompleteIntersectionLocalRing B)
    (hTor : ∃ n : ℕ, ∀ p : ℕ, n < p → IsZero (Tor[A, p](B, A ⧸ maximalIdeal A))) :
    IsCompleteIntersectionLocalRing A ∧
      RingHom.IsLocalCompleteIntersection (maximalIdealCompletionMap (algebraMap A B)) := sorry

/-- Proposition 23.9.2 (2): if `A` is a complete intersection and the induced map on
maximal-ideal completions `A^∧ → B^∧` is a local complete intersection homomorphism, then `B` is
a complete intersection and `Tor_p^A(B, A / 𝔪_A)` is nonzero for only finitely many `p`. -/
@[stacks 09QB]
theorem targetCompleteIntersection_torVanishing_of_sourceCompleteIntersection_completionMapLocalCompleteIntersection
    (hA : IsCompleteIntersectionLocalRing A)
    (hcomp :
      RingHom.IsLocalCompleteIntersection (maximalIdealCompletionMap (algebraMap A B))) :
    IsCompleteIntersectionLocalRing B ∧
      ∃ n : ℕ, ∀ p : ℕ, n < p → IsZero (Tor[A, p](B, A ⧸ maximalIdeal A)) := sorry

end
