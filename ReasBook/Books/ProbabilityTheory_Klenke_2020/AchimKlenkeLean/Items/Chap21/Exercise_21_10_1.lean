import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Theorem_21_64

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open OrderDual

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/- Exercise 21.10.1 is `source-facing`: the textbook variables `Y_n` are the unweighted quadratic
partition sums at the horizon `T = 1` from the proof of Theorem 21.64. Their
`core/canonical` owner is Chapter 21's pathwise construction
`weightedPartitionQuadraticVariationApproximationUpTo`; the only `bridge/view` content here is to
regard those pathwise sums as random variables and then as a reverse-time process on `ℕᵒᵈ`.

Primitive data:
* a real process `X : NNReal → Ω → ℝ`;
* an admissible partition sequence `P`.

Derived API:
* the random variables obtained by evaluating the pathwise partition sums on each sample point;
* the reverse-time process `n ↦ Y_n`, used in the backwards-martingale statement.
-/

/-- The unweighted quadratic partition sum along the `n`-th row of `P`, viewed as a real random
variable on `Ω`. -/
noncomputable def partitionQuadraticVariationApproximationUpToRandomVariable
    (X : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) (n : ℕ) : Ω → ℝ :=
  fun ω ↦
    weightedPartitionQuadraticVariationApproximationUpTo
      (fun _ ↦ (1 : ℝ)) (fun t ↦ X t ω) P T n

section

variable (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
omit [MeasurableSpace Ω]

/-- Unfolding the random-variable bridge returns the underlying pathwise quadratic partition sum. -/
theorem partitionQuadraticVariationApproximationUpToRandomVariable_def
    (X : NNReal → Ω → ℝ) (T : NNReal) (n : ℕ) :
    partitionQuadraticVariationApproximationUpToRandomVariable X P T n =
      fun ω ↦
        weightedPartitionQuadraticVariationApproximationUpTo
          (fun _ ↦ (1 : ℝ)) (fun t ↦ X t ω) P T n :=
  rfl

end

/-- The reverse-time process associated with the quadratic partition sums up to the horizon `T`. -/
noncomputable abbrev partitionQuadraticVariationApproximationUpToBackwardProcess
    (X : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) : ℕᵒᵈ → Ω → ℝ :=
  fun n ↦ partitionQuadraticVariationApproximationUpToRandomVariable X P T (ofDual n)

-- Proof sketch: each `Y_n` is a finite sum of products of the strongly measurable coordinates
-- `X (P n k)` and `X (partitionNextPointUpTo P n k T)`.
/-- Each quadratic partition-sum random variable is strongly measurable whenever the underlying
process is strongly measurable at every time. -/
theorem partitionQuadraticVariationApproximationUpToRandomVariable_stronglyMeasurable
    {X : NNReal → Ω → ℝ} (hX_meas : ∀ t, StronglyMeasurable (X t))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (T : NNReal) (n : ℕ) :
    StronglyMeasurable
      (partitionQuadraticVariationApproximationUpToRandomVariable X P T n) := by
  sorry

/-- The reverse-time quadratic partition-sum process is strongly measurable at every index. -/
theorem partitionQuadraticVariationApproximationUpToBackwardProcess_stronglyMeasurable
    {X : NNReal → Ω → ℝ} (hX_meas : ∀ t, StronglyMeasurable (X t))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕᵒᵈ) :
    StronglyMeasurable
      (partitionQuadraticVariationApproximationUpToBackwardProcess X P T n) := by
  simpa [partitionQuadraticVariationApproximationUpToBackwardProcess] using
    partitionQuadraticVariationApproximationUpToRandomVariable_stronglyMeasurable
      hX_meas P T (ofDual n)

namespace IsBrownianMotion

-- Proof sketch: for the admissible partition sequence `P`, the random variables from the proof of
-- Theorem 21.64 are exactly the reverse-time process obtained by specializing
-- `weightedPartitionQuadraticVariationApproximationUpTo` to the constant weight `1` and the
-- horizon `T = 1`; the Brownian bridge/independent-increments argument identifies them as a
-- backwards martingale.
/-- Exercise 21.10.1: for Brownian motion `W` and an admissible partition sequence `P`, the
random variables `Y_n = \sum_{t \in \mathcal P_1^n} (W_{t'} - W_t)^2` from the proof of
Theorem 21.64 form a backwards martingale. -/
theorem partitionQuadraticVariationApproximationUpTo_one_backwardsMartingale
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    Martingale
      (partitionQuadraticVariationApproximationUpToBackwardProcess W P 1)
      (Filtration.natural
        (partitionQuadraticVariationApproximationUpToBackwardProcess W P 1)
        (partitionQuadraticVariationApproximationUpToBackwardProcess_stronglyMeasurable
          hW.stronglyMeasurable P 1))
      μ := by
  sorry

end IsBrownianMotion

end ProbabilityTheory
