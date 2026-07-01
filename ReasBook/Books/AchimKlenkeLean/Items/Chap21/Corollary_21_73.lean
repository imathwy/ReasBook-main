import Mathlib
import AchimKlenkeLean.Items.Chap21.Definition_21_52
import AchimKlenkeLean.Items.Chap21.Definition_21_66
import AchimKlenkeLean.Items.Chap21.Theorem_21_70

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "PathSpace" => C(NNReal, ℝ)

variable {ℱ : TimeFiltration}

/-- A continuous quadratic-covariation process of continuous local martingales `M` and `N` is a
continuous adapted process `A`, starting at `0` and with almost surely locally finite variation,
such that `MN - A` is a continuous local martingale. -/
structure IsContinuousQuadraticCovariationProcess
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (M N A : NNReal → Ω → ℝ) : Prop where
  /-- The covariation process starts from `0`. -/
  zero : A 0 = 0
  /-- The covariation process is adapted to the ambient filtration. -/
  adapted : Adapted ℱ A
  /-- The covariation process has continuous sample paths. -/
  continuous : ∀ ω : Ω, Continuous (fun t : NNReal ↦ A t ω)
  /-- Almost every sample path of the covariation process has locally finite variation. -/
  locally_finite_variation :
    ∀ᵐ ω ∂μ,
      LocallyBoundedVariationOn
        (⟨fun t ↦ A t ω, continuous ω⟩ : PathSpace) Set.univ
  /-- Subtracting the covariation process from the pointwise product yields a local martingale. -/
  local_martingale_mul_sub :
    IsLocalMartingale ℱ μ (fun t ω ↦ M t ω * N t ω - A t ω)

/-- The mixed partition sum of `M` and `N` on `[0,T]` along the `n`-th row of an admissible
partition sequence. -/
def partitionQuadraticCovariationApproximationUpTo
    (M N : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) (ω : Ω) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    (M (partitionNextPointUpTo P n k T) ω - M (P n k) ω) *
      (N (partitionNextPointUpTo P n k T) ω - N (P n k) ω)

-- Proof sketch: unfold `partitionQuadraticCovariationApproximationUpTo`.
/-- Expanding `partitionQuadraticCovariationApproximationUpTo` gives the finite sum of mixed
increments along the truncated partition row. -/
theorem partitionQuadraticCovariationApproximationUpTo_def
    (M N : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) (ω : Ω) :
    partitionQuadraticCovariationApproximationUpTo M N P T n ω =
      Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
        (M (partitionNextPointUpTo P n k T) ω - M (P n k) ω) *
          (N (partitionNextPointUpTo P n k T) ω - N (P n k) ω) := sorry

-- Proof sketch: apply the square-variation existence theorem to `M + N` and `M - N`, define the
-- mixed bracket by the polarization identity `(1 / 4) * (⟨M + N⟩ - ⟨M - N⟩)`, use that a
-- difference of increasing continuous paths has locally finite variation, and prove uniqueness by
-- subtracting two candidates to obtain a continuous local martingale of locally finite variation.
/-- Corollary 21.73: if `M` and `N` are continuous local martingales, then there exists a unique
continuous adapted process starting at `0`, with almost surely locally finite variation, whose
subtraction from the product process `MN` is again a continuous local martingale. This process is
the quadratic covariation `⟨M,N⟩`. -/
theorem existsUnique_continuousQuadraticCovariationProcess
    {M N : NNReal → Ω → ℝ} (hM : M ∈ Mlocc ℱ μ) (hN : N ∈ Mlocc ℱ μ) :
    ∃! A : NNReal → Ω → ℝ, IsContinuousQuadraticCovariationProcess ℱ μ M N A := sorry

-- Proof sketch: write the mixed partition sums as the polarization combination of the quadratic
-- partition sums for `M + N` and `M - N`, invoke Theorem 21.70 (3) for those two square brackets,
-- and pass to the limit in probability through addition, subtraction, and scalar multiplication.
/-- Any continuous quadratic-covariation process `A` is the limit in probability of the mixed
partition sums along every admissible sequence of partitions, matching formula `(21.60)`. -/
theorem tendstoInMeasure_partitionQuadraticCovariationApproximationUpTo
    {M N A : NNReal → Ω → ℝ} (hM : M ∈ Mlocc ℱ μ) (hN : N ∈ Mlocc ℱ μ)
    (hA : IsContinuousQuadraticCovariationProcess ℱ μ M N A) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) :
    TendstoInMeasure μ
      (fun n : ℕ ↦ partitionQuadraticCovariationApproximationUpTo M N P T n)
      atTop (A T) := sorry

end ProbabilityTheory
