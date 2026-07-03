import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_1_12 (from Chap01) -/
universe u

/-- Lemma 1.12: a compact subset of a Hausdorff topological space is closed. -/
theorem isClosed_of_isCompact
    {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} :
    IsCompact C → IsClosed C :=
  IsCompact.isClosed
