import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_56
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Theorem_21_64

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- `HasPathwiseQuadraticVariationAlongSubsequence μ M P φ A` means that, for almost every sample
point, the quadratic partition sums of `M` along the partition-row subsequence `φ` converge at
every time `T` to the path `A`. -/
def HasPathwiseQuadraticVariationAlongSubsequence
    (μ : Measure Ω) (M : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (φ : ℕ → ℕ) (A : NNReal → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ T : NNReal,
    Tendsto
      (fun n : ℕ ↦
        weightedPartitionQuadraticVariationApproximationUpTo
          (fun _ ↦ (1 : ℝ)) (fun t ↦ M t ω) P T (φ n))
      atTop
      (𝓝 (A T ω))

-- Proof sketch: unfold `HasPathwiseQuadraticVariationAlongSubsequence`; the statement is exactly
-- the almost-sure simultaneous convergence of the partition-square sums along the subsequence `φ`.
/-- Unfolding `HasPathwiseQuadraticVariationAlongSubsequence` says that along the subsequence `φ`,
the quadratic partition sums converge almost surely for every time horizon to the comparison
process `A`. -/
theorem hasPathwiseQuadraticVariationAlongSubsequence_iff
    (μ : Measure Ω) (M : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (φ : ℕ → ℕ) (A : NNReal → Ω → ℝ) :
    HasPathwiseQuadraticVariationAlongSubsequence μ M P φ A ↔
      ∀ᵐ ω ∂μ, ∀ T : NNReal,
        Tendsto
          (fun n : ℕ ↦
            weightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ)) (fun t ↦ M t ω) P T (φ n))
          atTop
          (𝓝 (A T ω)) := sorry

-- Proof sketch: enumerate the nonnegative rationals, extract a diagonal subsequence of partition
-- rows that preserves almost-sure convergence at each rational time, then use the monotonicity and
-- continuity of `T ↦ U_T^n` and `T ↦ A_T` to upgrade convergence from `ℚ≥0` to all `T ≥ 0`.
/-- Remark 21.71: if every nonnegative rational time admits a subsequence of partition rows along
which the quadratic partition sums of `M` converge almost surely to a continuous monotone process
`A`, then one can choose a single subsequence of rows for which this convergence holds almost
surely for every `T ≥ 0`; equivalently, along that subsequence the pathwise quadratic variation of
`M` agrees almost surely with `A`. -/
theorem exists_partition_subsequence_with_ae_pathwise_quadratic_variation
    {μ : Measure Ω} {M : NNReal → Ω → ℝ} {P : ℕ → ℕ → NNReal}
    [IsAdmissiblePartitionSequence P] {A : NNReal → Ω → ℝ}
    (hU_mono :
      ∀ n : ℕ, ∀ ω : Ω,
        Monotone fun T : NNReal ↦
          weightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) (fun t ↦ M t ω) P T n)
    (hU_cont :
      ∀ n : ℕ, ∀ ω : Ω,
        Continuous fun T : NNReal ↦
          weightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) (fun t ↦ M t ω) P T n)
    (hA_mono : ∀ ω : Ω, Monotone fun T : NNReal ↦ A T ω)
    (hA_cont : ∀ ω : Ω, Continuous fun T : NNReal ↦ A T ω)
    (hsubseq_rat :
      ∀ q : ℚ≥0,
        ∃ φ : {φ : ℕ → ℕ // StrictMono φ},
          ∀ᵐ ω ∂μ,
            Tendsto
              (fun n : ℕ ↦
                weightedPartitionQuadraticVariationApproximationUpTo
                  (fun _ ↦ (1 : ℝ)) (fun t ↦ M t ω) P q (φ.1 n))
              atTop
              (𝓝 (A q ω))) :
    ∃ φ : {φ : ℕ → ℕ // StrictMono φ},
      HasPathwiseQuadraticVariationAlongSubsequence μ M P φ.1 A := sorry

end ProbabilityTheory
