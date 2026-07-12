import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.50.4: if `A` is a valuation ring with fraction field `K`, then for every `x : K`
either `x ∈ A` or `x⁻¹ ∈ A` or both. In mathlib the canonical form is
`ValuationRing.isInteger_or_isInteger`, stated using `IsLocalization.IsInteger`; under the
fraction-field hypotheses this is the precise library-facing formulation of the Stacks statement. -/
recall ValuationRing.isInteger_or_isInteger
