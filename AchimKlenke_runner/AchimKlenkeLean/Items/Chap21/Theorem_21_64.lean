import Mathlib
import AchimKlenkeLean.Items.Chap21.Definition_21_8
import AchimKlenkeLean.Items.Chap21.Definition_21_56

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory BigOperators

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The weighted quadratic partition sum of a real-valued path on `[0,T]` along the `n`-th row of
an admissible partition sequence. -/
def weightedPartitionQuadraticVariationApproximationUpTo
    (f : NNReal → ℝ) (X : NNReal → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    f (P n k) * (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2

-- Proof sketch: this is definitional after unfolding
-- `weightedPartitionQuadraticVariationApproximationUpTo`.
/-- Expanding `weightedPartitionQuadraticVariationApproximationUpTo` gives the weighted sum of
squared increments along the truncated partition row. -/
@[simp] theorem weightedPartitionQuadraticVariationApproximationUpTo_def
    (f : NNReal → ℝ) (X : NNReal → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) (n : ℕ) :
    weightedPartitionQuadraticVariationApproximationUpTo f X P T n =
      Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
        f (P n k) * (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2 := rfl

namespace IsBrownianMotion

-- Proof sketch: for rational `T`, reduce by Brownian scaling to `T = 1`, compute the expectation
-- and variance of the quadratic partition sums, and use almost-sure convergence along the
-- admissible sequence. Then pass from rational times to all `T : NNReal` by monotonicity and
-- continuity of Brownian paths.
/-- Theorem 21.64: for Brownian motion `W` and every admissible sequence of partitions `P`, the
quadratic partition sums along `P` converge almost surely to `T` simultaneously for all
`T ≥ 0`; equivalently, the quadratic variation satisfies `⟨W⟩_T = T`. -/
theorem ae_tendsto_partitionQuadraticVariationApproximationUpTo
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    ∀ᵐ ω ∂μ, ∀ T : NNReal,
      Tendsto
        (fun n : ℕ ↦
          weightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) (fun t ↦ W t ω) P T n)
        atTop (nhds (T : ℝ)) := sorry

end IsBrownianMotion

end ProbabilityTheory
