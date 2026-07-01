import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The partial sum `X₁ + ⋯ + Xₙ` of a real-valued sequence of random variables, written with the
chapter's `0`-based indexing as the sum of `X 0, …, X (n - 1)`. -/
def partialRealSum (X : ℕ → Ω → ℝ) (n : ℕ+) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range (n : ℕ), X i ω

/-- The Legendre-transform rate function associated with the cumulant-generating function of `X`
under the measure `P`. -/
def legendreCgfRateFunction (X : Ω → ℝ) (P : Measure Ω) (x : ℝ) : EReal :=
  sSup (Set.range fun t : ℝ ↦ ((t * x - cgf X P t : ℝ) : EReal))

/-- The law of the normalized partial sum `n⁻¹ (X₁ + ⋯ + Xₙ)`. -/
def normalizedPartialSumLaw (X : ℕ → Ω → ℝ) (P : Measure Ω) (n : ℕ+) : Measure ℝ :=
  Measure.map (fun ω ↦ partialRealSum X n ω / (n : ℝ)) P

/-- The large-deviation upper bound for a sequence of probability laws on `ℝ` with speed `n` and
rate function `I`, tested on closed sets. -/
def HasLargeDeviationUpperBound (μ : ℕ+ → Measure ℝ) (I : ℝ → EReal) : Prop :=
  ∀ s : Set ℝ, IsClosed s →
    Filter.limsup (fun n : ℕ+ ↦ ENNReal.log (μ n s) / (n : EReal)) atTop ≤ -sInf (I '' s)

/-- The large-deviation lower bound for a sequence of probability laws on `ℝ` with speed `n` and
rate function `I`, tested on open sets. -/
def HasLargeDeviationLowerBound (μ : ℕ+ → Measure ℝ) (I : ℝ → EReal) : Prop :=
  ∀ s : Set ℝ, IsOpen s →
    -sInf (I '' s) ≤ Filter.liminf (fun n : ℕ+ ↦ ENNReal.log (μ n s) / (n : EReal)) atTop

/-- A sequence of laws on `ℝ` satisfies the large deviation principle with speed `n` and rate
function `I` if it satisfies the standard closed-set upper bound and open-set lower bound. -/
def SatisfiesLargeDeviationPrinciple (μ : ℕ+ → Measure ℝ) (I : ℝ → EReal) : Prop :=
  HasLargeDeviationUpperBound μ I ∧ HasLargeDeviationLowerBound μ I

-- Proof sketch: this is exactly the first projection of the conjunction in
-- `SatisfiesLargeDeviationPrinciple`.
/-- Extract the closed-set upper bound from a large deviation principle. -/
theorem SatisfiesLargeDeviationPrinciple.upper
    {μ : ℕ+ → Measure ℝ} {I : ℝ → EReal}
    (h : SatisfiesLargeDeviationPrinciple μ I) :
    HasLargeDeviationUpperBound μ I := sorry

-- Proof sketch: this is exactly the second projection of the conjunction in
-- `SatisfiesLargeDeviationPrinciple`.
/-- Extract the open-set lower bound from a large deviation principle. -/
theorem SatisfiesLargeDeviationPrinciple.lower
    {μ : ℕ+ → Measure ℝ} {I : ℝ → EReal}
    (h : SatisfiesLargeDeviationPrinciple μ I) :
    HasLargeDeviationLowerBound μ I := sorry

-- Proof sketch: combine Cramér's theorem for half-lines with the monotonicity and convexity of
-- the Legendre-transform rate function, use the law of large numbers to control intervals
-- containing `0`, and then pass from intervals to arbitrary closed and open sets by the standard
-- reduction arguments from the example.
/-- Example 23.10: the laws of the normalized partial sums of an i.i.d. real sequence with finite
exponential moments satisfy the large deviation principle on `ℝ`, with rate function given by the
Legendre transform of the cumulant-generating function of the common law. -/
theorem normalizedPartialSumLaw_satisfies_cramer_largeDeviationPrinciple
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P) :
    SatisfiesLargeDeviationPrinciple (normalizedPartialSumLaw X P)
      (legendreCgfRateFunction (X 0) P) := sorry

end ProbabilityTheory
