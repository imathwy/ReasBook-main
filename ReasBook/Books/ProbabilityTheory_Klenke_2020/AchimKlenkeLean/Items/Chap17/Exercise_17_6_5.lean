import ProbabilityTheory_Klenke_2020.Items.Chap17.Example_17_52
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

private def resetWalkTransientExampleSequenceReal : ℕ → ℝ :=
  fun n ↦ 1 - 1 / (n + 2 : ℝ) ^ (2 : ℕ)

-- Proof sketch: `1 / (n + 2)^2` lies in `[0, 1]` for every `n`, so subtracting it from `1`
-- again gives a value in `[0, 1]`.
private theorem resetWalkTransientExampleSequenceReal_isProbabilitySequence :
    IsResetWalkProbabilitySequence resetWalkTransientExampleSequenceReal := sorry

/-- A transient example sequence for the reset walk, with square-summable defects `1 - p_n`. -/
def resetWalkTransientExampleSequence : ResetWalkParameters :=
  ⟨resetWalkTransientExampleSequenceReal,
    resetWalkTransientExampleSequenceReal_isProbabilitySequence⟩

private def resetWalkNullRecurrentExampleSequenceReal : ℕ → ℝ :=
  fun n ↦ 1 - 1 / (n + 2 : ℝ)

-- Proof sketch: since `n + 2 ≥ 2`, the harmonic term `1 / (n + 2)` lies in `[0, 1 / 2]`,
-- hence `1 - 1 / (n + 2)` lies in `[1 / 2, 1]`.
private theorem resetWalkNullRecurrentExampleSequenceReal_isProbabilitySequence :
    IsResetWalkProbabilitySequence resetWalkNullRecurrentExampleSequenceReal := sorry

/-- A null recurrent example sequence for the reset walk, with harmonic defects `1 - p_n`. -/
def resetWalkNullRecurrentExampleSequence : ResetWalkParameters :=
  ⟨resetWalkNullRecurrentExampleSequenceReal,
    resetWalkNullRecurrentExampleSequenceReal_isProbabilitySequence⟩

private def resetWalkPositiveRecurrentExampleSequenceReal : ℕ → ℝ :=
  fun _ ↦ 1 / 2

-- Proof sketch: the constant value `1 / 2` lies in `[0, 1]`.
private theorem resetWalkPositiveRecurrentExampleSequenceReal_isProbabilitySequence :
    IsResetWalkProbabilitySequence resetWalkPositiveRecurrentExampleSequenceReal := sorry

/-- A positive recurrent geometric example sequence for the reset walk. -/
def resetWalkPositiveRecurrentExampleSequence : ResetWalkParameters :=
  ⟨resetWalkPositiveRecurrentExampleSequenceReal,
    resetWalkPositiveRecurrentExampleSequenceReal_isProbabilitySequence⟩

private def resetWalkDyadicSpikeSequenceReal : ℕ → ℝ :=
  fun n ↦
    if 2 ^ Nat.log2 n = n then
      1 / 3
    else
      1 - 1 / (n + 2 : ℝ) ^ (2 : ℕ)

-- Proof sketch: both branches lie in `[0, 1]`: the spike branch is the constant `1 / 3`, and
-- the background branch is the transient example sequence.
private theorem resetWalkDyadicSpikeSequenceReal_isProbabilitySequence :
    IsResetWalkProbabilitySequence resetWalkDyadicSpikeSequenceReal := sorry

/-- A dyadic-spike sequence for the reset walk: at powers of two the upward-jump probability is
`1 / 3`, while away from powers of two the defects are square-summable. -/
def resetWalkDyadicSpikeSequence : ResetWalkParameters :=
  ⟨resetWalkDyadicSpikeSequenceReal, resetWalkDyadicSpikeSequenceReal_isProbabilitySequence⟩

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}

section ResetWalkRealization

variable {p : ResetWalkParameters}
variable [IsMarkovProcessRealization (fun n ↦ resetWalkKernel p ^ n) P X]

/- Exercise 17.6.5 (1): this recurrence criterion is already the source-facing reset-walk theorem
from Example 17.52. -/
recall resetWalk_isRecurrentMarkovChain_iff_not_summable_one_sub

-- Proof sketch: use the tail-sum formula `𝔼[τ] = ∑_{n ≥ 0} ℙ(τ > n)` for the first return time to
-- `0`; for the reset walk, the survival probability `ℙ_0(τ_0^1 > n)` is exactly the prefix
-- product `∏_{k < n} p_k`.
/-- Exercise 17.6.5 (2): the expected first return time to `0` in the reset walk is the series
`M = ∑_{n=0}^\infty ∏_{k=0}^{n-1} p_k`, represented here by `resetWalkMassSeries p`. -/
theorem expectedFirstReturnTime_resetWalk_zero_eq_massSeries :
    expectedFirstReturnTime P X 0 = resetWalkMassSeries p := sorry

/- Exercise 17.6.5 (3): this positive-recurrence criterion is already the source-facing
reset-walk theorem from Example 17.52. -/
recall resetWalk_isPositiveRecurrentMarkovChain_iff_massSeries_lt_top

end ResetWalkRealization

section TransientExample

variable [IsMarkovProcessRealization
  (fun n ↦ resetWalkKernel resetWalkTransientExampleSequence ^ n) P X]

-- Proof sketch: for `resetWalkTransientExampleSequence`, the defect series
-- `∑ 1 / (n + 2)^2` is summable, so part (1) gives nonrecurrence; irreducibility of the reset
-- walk then identifies the regime as one where every state is transient, hence Definition 17.30
-- applies vacuously.
/-- Exercise 17.6.5 (4): part (iii)(a). The sequence
`p_n = 1 - 1 / (n + 2)^2` gives a transient reset walk. -/
theorem resetWalkTransientExample_isTransientMarkovChain :
    IsTransientMarkovChain (resetWalkTransitionMatrix resetWalkTransientExampleSequence) P X :=
  sorry

end TransientExample

section NullRecurrentExample

variable [IsMarkovProcessRealization
  (fun n ↦ resetWalkKernel resetWalkNullRecurrentExampleSequence ^ n) P X]

-- Proof sketch: for `p_n = 1 - 1 / (n + 2)`, the defect series is harmonic and hence divergent,
-- while the prefix products are comparable to `1 / (n + 1)`, so the return-time series is
-- infinite. Parts (1) and (3) therefore give recurrence but not positive recurrence.
/-- Exercise 17.6.5 (5): part (iii)(b). The sequence
`p_n = 1 - 1 / (n + 2)` gives a null recurrent reset walk. -/
theorem resetWalkNullRecurrentExample_isNullRecurrentMarkovChain :
    IsNullRecurrentMarkovChain P X := sorry

end NullRecurrentExample

section PositiveRecurrentExample

variable [IsMarkovProcessRealization
  (fun n ↦ resetWalkKernel resetWalkPositiveRecurrentExampleSequence ^ n) P X]

-- Proof sketch: for the constant choice `p_n = 1 / 2`, the prefix products form a geometric
-- sequence, so `M` is finite; part (3) then yields positive recurrence.
/-- Exercise 17.6.5 (6): part (iii)(c). The constant sequence `p_n = 1 / 2` gives a positive
recurrent reset walk. -/
theorem resetWalkPositiveRecurrentExample_isPositiveRecurrentMarkovChain :
    IsPositiveRecurrentMarkovChain P X := sorry

end PositiveRecurrentExample

section DyadicSpikeExample

variable [IsMarkovProcessRealization
  (fun n ↦ resetWalkKernel resetWalkDyadicSpikeSequence ^ n) P X]

-- Proof sketch: each dyadic spike contributes a factor `1 / 3` to the prefix product, so along
-- the interval `[2^m, 2^(m + 1))` the product is bounded by a multiple of `3^{-m}`; this makes
-- the mass series `M` summable, and part (3) yields positive recurrence.
/-- Exercise 17.6.5 (7): part (iii)(d). The dyadic-spike sequence gives a positive recurrent reset
walk. -/
theorem resetWalkDyadicSpikeExample_isPositiveRecurrentMarkovChain :
    IsPositiveRecurrentMarkovChain P X := sorry

end DyadicSpikeExample

-- Proof sketch: up to time `n`, the dyadic spikes contribute about `(2 / 3) log₂ n` to the defect
-- sum, while the square-summable background contributes only a bounded amount. Hence the
-- exponential comparison terms are comparable to `n^{-2 / (3 * log 2)}`, whose exponent is
-- strictly smaller than `1`, so the series is not summable.
/-- Exercise 17.6.5 (8): part (iii)(d). For the dyadic-spike sequence, the exponential comparison
series `∑ exp ( - ∑_{k < n} (1 - p_k))` is still divergent. -/
theorem resetWalkDyadicSpikeExample_expSeries_not_summable :
    ¬ Summable
      (fun n ↦
        Real.exp
          (-Finset.sum (Finset.range n) (fun k ↦ 1 - resetWalkDyadicSpikeSequence k))) := sorry

end ProbabilityTheory
