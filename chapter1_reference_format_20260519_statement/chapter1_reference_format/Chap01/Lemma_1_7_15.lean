import Mathlib
import chapter1_reference_format.Chap01.Lemma_1_1_15

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {S : Type u} [PartialOrder S] [IsWellOrder S (· < ·)]

-- Proof sketch: endow `S` with the linear order canonically induced by the well-ordering, then
-- reuse the earlier chapter bridge from least elements of nonempty subsets to totality of `≤`.
/-- Lemma 1.7.15: every well-ordered set is totally ordered. -/
theorem isLinearOrder_of_isWellOrder :
    IsLinearOrder S (· ≤ ·) := by
  exact total_of_nonempty_set_has_isLeast
    (isWellOrder_iff_nonempty_subsets_have_least.1 ‹IsWellOrder S (· < ·)›)
