import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_20 (from Items/Chap06) -/
open MeasureTheory
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/- Definition 6.20: A family in `ℒ^p(μ)` is formalized as a subset of the normed space
`MeasureTheory.Lp ℝ p μ`; boundedness of such a family is the canonical bornological notion
`Bornology.IsBounded`, equivalently uniform boundedness of the `Lp` norms. -/
recall Bornology.IsBounded
