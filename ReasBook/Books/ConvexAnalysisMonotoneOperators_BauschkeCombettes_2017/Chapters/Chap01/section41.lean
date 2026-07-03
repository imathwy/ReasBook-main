import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_1_41 (from Chap01) -/
universe u

variable {X : Type u} [MetricSpace X] {C : Set X}

/-- Lemma 1.41: a compact subset of a metric space is closed and bounded. -/
theorem isClosed_and_isBounded_of_isCompact (hC : IsCompact C) :
    IsClosed C ∧ Bornology.IsBounded C := by
  exact ⟨hC.isClosed, hC.isBounded⟩
