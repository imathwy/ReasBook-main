import Mathlib
import AchimKlenkeLean.Items.Chap02.Definition_2_14
import AchimKlenkeLean.Items.Chap16.Definition_16_1
import AchimKlenkeLean.Items.Chap24.Definition_24_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open MeasureTheory.ProbabilityMeasure

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [TopologicalSpace E]

/-- Definition 24.20: a random measure is infinitely divisible if, for every positive integer
`n`, it can be written as the sum of `n` iid random measures on the same probability space. -/
def IsInfinitelyDivisibleRandomMeasure
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) : Prop :=
  ∀ n : ℕ+, ∃ Y : Fin n → Ω → Measure E,
    (∀ i, IsRandomMeasure P (Y i)) ∧
    IsIID Y (P : Measure Ω) ∧
    X = ∑ i, Y i

-- Proof sketch: apply the defining decomposition property with `n = 1`; then `X` is the singleton
-- sum of a random measure, so `X` itself is a random measure.
/-- An infinitely divisible random measure is, in particular, a random measure. -/
theorem IsInfinitelyDivisibleRandomMeasure.isRandomMeasure
    {P : ProbabilityMeasure Ω} {X : Ω → Measure E}
    (hX : IsInfinitelyDivisibleRandomMeasure P X) :
    IsRandomMeasure P X := sorry

-- Proof sketch: view `X` as a `Measure E`-valued additive random variable. The source-facing
-- pathwise decomposition yields the Chapter 16 bridge notion
-- `IsInfinitelyDivisibleRandomVariable (P : Measure Ω) X`, so the canonical owner theorem
-- `isInfinitelyDivisibleRandomVariable_iff_law_isInfinitelyDivisible` gives infinite divisibility
-- of the pushed-forward law.
/-- The law of an infinitely divisible random measure is infinitely divisible in the canonical
owner sense on `ProbabilityMeasure (Measure E)`. -/
theorem IsInfinitelyDivisibleRandomMeasure.law_isInfinitelyDivisible
    {P : ProbabilityMeasure Ω} {X : Ω → Measure E}
    (hX : IsInfinitelyDivisibleRandomMeasure P X) :
    IsInfinitelyDivisible (ProbabilityMeasure.map P hX.isRandomMeasure.aemeasurable) := sorry

end ProbabilityTheory
