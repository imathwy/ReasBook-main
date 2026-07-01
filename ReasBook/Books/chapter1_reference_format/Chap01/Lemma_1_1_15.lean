import Mathlib
import chapter1_reference_format.Chap01.Definition_1_1_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

variable {S : Type u} [PartialOrder S]

-- Proof sketch: first use Definition 1.1.14 to upgrade the least-element hypothesis to the
-- canonical owner `IsWellOrder S (· < ·)`, then use trichotomy for `<` to deduce totality of `≤`.
/-- Lemma 1.1.15: a partial order in which every nonempty subset has a least element is total. -/
theorem total_of_nonempty_set_has_isLeast
    (h : ∀ s : Set S, s.Nonempty → ∃ a, IsLeast s a) :
    IsLinearOrder S (· ≤ ·) := by
  have hwo : IsWellOrder S (· < ·) :=
    isWellOrder_iff_nonempty_subsets_have_least.2 fun s hs ↦ by
      rcases h s hs with ⟨a, ha⟩
      exact ⟨a, ha.1, ha.2⟩
  letI : IsWellOrder S (· < ·) := hwo
  refine { toIsPartialOrder := inferInstance, toTotal := ?_ }
  exact ⟨fun a b ↦ by
    rcases trichotomous_of (· < ·) a b with hab | rfl | hba
    · exact Or.inl (le_of_lt hab)
    · exact Or.inl le_rfl
    · exact Or.inr (le_of_lt hba)
  ⟩
