import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set MeasureTheory MeasurableSpace

/-- The modified finite interval `F_n = [-n / 2, (n + 1) / 2] ∩ ℤ` from the example, written as an
interval in `ℤ`. -/
def integerAlternatingSegment (n : ℕ) : Set ℤ :=
  Set.Icc (-((n : ℤ) / 2)) (((n : ℤ) + 1) / 2)

/-- Example 1.43: the modified family `F_n = [-n / 2, (n + 1) / 2] ∩ ℤ` on `ℤ`, used in the
example as a `π`-system generator of the full powerset with finite exhausting pieces. -/
def integerAlternatingGenerator : Set (Set ℤ) :=
  Set.range integerAlternatingSegment

-- Proof sketch: the left endpoint moves weakly left and the right endpoint moves weakly right
-- with `n`, so the intervals form an increasing sequence.
/-- The modified intervals `F_n` form an increasing sequence. -/
theorem integerAlternatingSegment_monotone :
    Monotone integerAlternatingSegment := sorry

-- Proof sketch: intervals in `ℤ` are finite because `ℤ` is a locally finite order.
/-- Each modified interval `F_n` is a finite subset of `ℤ`. -/
theorem integerAlternatingSegment_finite (n : ℕ) :
    (integerAlternatingSegment n).Finite := sorry

-- Proof sketch: any two members of the increasing chain have nonempty intersection, since they all
-- contain `0`.
/-- The modified generator family is a `π`-system. -/
theorem integerAlternatingGenerator_isPiSystem :
    IsPiSystem integerAlternatingGenerator := sorry

private theorem zero_mem_integerAlternatingSegment (n : ℕ) :
    (0 : ℤ) ∈ integerAlternatingSegment n := by
  rw [integerAlternatingSegment, Set.mem_Icc]
  omega

/-- Textbook companion: the modified generator family is intersection-closed. -/
theorem integerAlternatingGenerator_isInterClosed :
    IsInterClosed integerAlternatingGenerator := by
  refine ⟨?_⟩
  intro s t hs ht
  rcases hs with ⟨m, rfl⟩
  rcases ht with ⟨n, rfl⟩
  exact integerAlternatingGenerator_isPiSystem _ (mem_range_self m) _ (mem_range_self n)
    ⟨0, zero_mem_integerAlternatingSegment m, zero_mem_integerAlternatingSegment n⟩

-- Proof sketch: the family is increasing and `F_{2k}` and `F_{2k+1}` add one new singleton at a
-- time, so every singleton is measurable in the generated `σ`-algebra; then Exercise 1.1.4 gives
-- the full powerset on the countable discrete space `ℤ`.
/-- The modified generator family generates the full measurable space on `ℤ`. -/
theorem generateFrom_integerAlternatingGenerator_eq_top :
    MeasurableSpace.generateFrom integerAlternatingGenerator = ⊤ := sorry

-- Proof sketch: the intervals are increasing and their endpoints tend to `-∞` and `+∞`, so every
-- integer eventually lies in the chain.
/-- The modified intervals exhaust `ℤ`. -/
theorem iUnion_integerAlternatingSegment_eq_univ :
    (⋃ n : ℕ, integerAlternatingSegment n) = (Set.univ : Set ℤ) := sorry

-- Proof sketch: on the countable space `ℤ`, `SigmaFinite` is equivalent to finite mass on each
-- singleton; combine this with finiteness of `F_n` and finite additivity on finite unions.
/-- Every sigma-finite measure on `ℤ` assigns finite mass to each modified interval `F_n`. -/
theorem measure_integerAlternatingSegment_lt_top (μ : Measure ℤ) [SigmaFinite μ] (n : ℕ) :
    μ (integerAlternatingSegment n) < ⊤ := sorry

-- Proof sketch: Example 1.43 verifies the standard uniqueness-theorem hypothesis by taking the
-- concrete spanning sequence `F_n` itself.
/-- Every sigma-finite measure on `ℤ` has finite spanning sets inside the modified generator
family, witnessed by the sequence `F_n`. -/
def finiteSpanningSetsIn_integerAlternatingGenerator (μ : Measure ℤ) [SigmaFinite μ] :
    μ.FiniteSpanningSetsIn integerAlternatingGenerator :=
  .mk integerAlternatingSegment
    (fun n ↦ ⟨n, rfl⟩)
    (measure_integerAlternatingSegment_lt_top μ)
    iUnion_integerAlternatingSegment_eq_univ
