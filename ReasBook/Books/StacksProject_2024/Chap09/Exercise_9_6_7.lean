import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Data.Rat.Cardinal
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open Cardinal IntermediateField

/- Domain-style sampling for countable generation of field extensions by adjoining subsets:
- same-domain declarations inspected:
  `IntermediateField.adjoin`,
  `IntermediateField.cardinalMk_adjoin_le`,
  `Cardinal.mkRat`,
  `not_countable_complex`
- owner abstraction: `IntermediateField.adjoin`

Layer triage:
- `source-facing`: the exercise statement that no countable subset of `ℂ` generates `ℂ` over `ℚ`
- `core/canonical`: the intermediate field `adjoin ℚ s`
- `bridge/view`: the canonical cardinality bound `cardinalMk_adjoin_le` together with the
  uncountability theorem `not_countable_complex`

Primitive data is just the owner object `adjoin ℚ s`. Countability of the generated intermediate
field is derived API from the canonical cardinality estimate, so this file should remain a thin
bridge theorem rather than introducing any local wrapper for countable generation. -/

/-- Exercise 9.6.7: no countable subset of `ℂ` generates `ℂ` as a field extension of `ℚ`. -/
-- Proof sketch: if `s` is countable, then `IntermediateField.adjoin ℚ s` has cardinality at most
-- `ℵ₀` by the cardinality bound for adjoins over a countable base. But `ℂ` is uncountable, so the
-- adjoin cannot be all of `ℂ`.
theorem complex_not_countably_generated_over_rat
    (s : Set ℂ) (hs : s.Countable) : adjoin ℚ s ≠ ⊤ := by
  intro htop
  have hadjoin : #(adjoin ℚ s) ≤ ℵ₀ := by
    calc
      #(adjoin ℚ s) ≤ #ℚ ⊔ #s ⊔ ℵ₀ := cardinalMk_adjoin_le ℚ s
      _ = ℵ₀ := by
        rw [Cardinal.mkRat, sup_assoc, sup_eq_right.2 hs.le_aleph0, sup_eq_right.2 le_rfl]
  have hs' : (adjoin ℚ s : Set ℂ).Countable := le_aleph0_iff_set_countable.mp hadjoin
  have huniv : (Set.univ : Set ℂ).Countable := by simpa [htop] using hs'
  exact not_countable_complex huniv
