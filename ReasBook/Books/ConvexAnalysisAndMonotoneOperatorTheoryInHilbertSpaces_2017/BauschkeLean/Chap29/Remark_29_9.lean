import Mathlib
import BauschkeLean.Chap03.Proposition_3_20

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Semantic recall: mathlib offers compactness-based nonempty-intersection lemmas for nested closed
-- sets, but the source-facing owner for this bounded closed convex Hilbert-space statement is
-- Proposition 3.20 in this project.
/-- Remark 29.9: in the setting of Proposition 29.8, the hypothesis
`(⋂ n : ℕ, C n).Nonempty` holds if `C 0` is bounded. -/
theorem nonempty_iInter_of_nonempty_isBounded_zero_isClosed_convex_of_succ_subset
    (C : ℕ → Set H) (h_nonempty : ∀ n, (C n).Nonempty)
    (h_bounded_zero : Bornology.IsBounded (C 0)) (h_closed : ∀ n, IsClosed (C n))
    (h_convex : ∀ n, Convex ℝ (C n)) (h_succ : ∀ n, C (n + 1) ⊆ C n) :
    (⋂ n : ℕ, C n).Nonempty := by
  have h_anti : Antitone C := antitone_nat_of_succ_le h_succ
  exact
    nonempty_iInter_of_nonempty_bounded_isClosed_convex C h_nonempty
      (fun n ↦ h_bounded_zero.subset (h_anti (Nat.zero_le n))) h_closed h_convex h_anti

end
