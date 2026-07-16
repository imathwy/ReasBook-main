import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_58
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_66
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Theorem_21_64

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration NNReal mΩ}

/-- A continuous square-variation process of a continuous local martingale `M` is an adapted
real-valued process `A` starting at `0`, with continuous increasing sample paths, such that
`M² - A` is a local martingale. -/
structure IsContinuousSquareVariationProcess
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω)
    (M A : NNReal → Ω → ℝ) : Prop where
  zero : A 0 = 0
  adapted : Adapted ℱ A
  continuous : ∀ ω : Ω, Continuous (fun t : NNReal ↦ A t ω)
  monotone : ∀ ω : Ω, Monotone (fun t : NNReal ↦ A t ω)
  local_martingale_sq_sub :
    IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω ^ 2 - A t ω)

-- Proof sketch: localize `M` by bounded stopped martingales, construct the `L²` limits of the
-- quadratic partition sums for the stopped processes, patch the resulting increasing continuous
-- processes together along the localizing sequence, and prove uniqueness by applying the finite
-- variation argument to the difference of two candidates.
/-- Theorem 21.70 (1): every continuous local martingale admits a unique continuous increasing
adapted process starting at `0` whose subtraction from the squared martingale yields a continuous
local martingale. -/
theorem existsUnique_continuousSquareVariationProcess
    {M : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M) :
    ∃! A : NNReal → Ω → ℝ, IsContinuousSquareVariationProcess ℱ μ M A := sorry

/-- The canonical square-variation process `⟨M⟩` attached to a continuous local martingale `M`. -/
noncomputable def continuousSquareVariationProcess
    {M : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M) :
    NNReal → Ω → ℝ :=
  Classical.choose (ExistsUnique.exists (existsUnique_continuousSquareVariationProcess hM))

private noncomputable def continuousSquareVariationBracket
    (M : NNReal → Ω → ℝ) (hM : IsContinuousLocalMartingale ℱ μ M) :
    NNReal → Ω → ℝ :=
  continuousSquareVariationProcess hM

scoped notation "⟨" M "⟩[" hM "]" =>
  continuousSquareVariationBracket M hM

-- Proof sketch: unfold `continuousSquareVariationProcess`; by construction it is the witness
-- chosen from the unique-existence statement in part (1).
/-- The chosen process `continuousSquareVariationProcess hM` satisfies the square-variation axioms
for `M`. -/
theorem isContinuousSquareVariationProcess_continuousSquareVariationProcess
    {M : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M) :
    IsContinuousSquareVariationProcess ℱ μ M (continuousSquareVariationProcess hM) := by
  exact Classical.choose_spec
    (ExistsUnique.exists (existsUnique_continuousSquareVariationProcess hM))

-- Proof sketch: both processes satisfy the defining square-variation property, so uniqueness in
-- part (1) identifies any such process with the canonical choice.
/-- Any continuous square-variation process for `M` agrees with the canonical bracket process
`continuousSquareVariationProcess hM`. -/
theorem continuousSquareVariationProcess_eq
    {M A : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (hA : IsContinuousSquareVariationProcess ℱ μ M A) :
    continuousSquareVariationProcess hM = A := by
  exact ExistsUnique.unique
    (existsUnique_continuousSquareVariationProcess hM)
    (isContinuousSquareVariationProcess_continuousSquareVariationProcess hM)
    hA

-- Proof sketch: use part (1) to pick the unique square-variation process `A`; for a continuous
-- square-integrable martingale, localize `M² - A`, apply optional sampling and uniform
-- integrability of the stopped squared martingale, and pass to the limit to upgrade the
-- local-martingale statement to a genuine martingale statement.
/-- Theorem 21.70 (2): if `M` is a continuous square-integrable martingale and `A` is its square
variation process from part (1), then `M² - A` is a martingale. -/
theorem martingale_sq_sub_of_continuousSquareVariationProcess
    {M A : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (hM_mart : Martingale M ℱ μ)
    (hM_sq : ∀ t : NNReal, Integrable (fun ω ↦ (M t ω) ^ 2) μ)
    (hA : IsContinuousSquareVariationProcess ℱ μ M A) :
    Martingale (fun t ω ↦ M t ω ^ 2 - A t ω) ℱ μ := sorry

-- Proof sketch: first prove the claim for bounded continuous martingales by showing that the
-- quadratic partition sums form an `L²`-Cauchy sequence; identify the limit with the square
-- variation process, and then pass to a general continuous local martingale by localization.
/-- Theorem 21.70 (3): for every admissible sequence of partitions, the quadratic partition sums of
`M` converge in probability at each fixed time `T` to the value `A T`, where `A` is the square
variation process from part (1). -/
theorem tendstoInMeasure_partitionQuadraticVariationApproximationUpTo
    {M A : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (hA : IsContinuousSquareVariationProcess ℱ μ M A) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) :
    TendstoInMeasure μ
      (fun n ω ↦
          weightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) (fun t ↦ M t ω) P T n)
      atTop (A T) := sorry

-- Proof sketch: apply Theorem 21.70 (3) to the canonical bracket process
-- `continuousSquareVariationProcess hM`, then upgrade the dyadic convergence along the fixed
-- dyadic partitions to the source-facing `HasSquareVariationAlong` statement on a full-measure set
-- of sample paths.
/-- Bridge/view theorem: for a continuous local martingale, almost every sample path has dyadic
square variation realized by the canonical bracket `continuousSquareVariationProcess hM`. -/
theorem ae_hasSquareVariationAlong_continuousSquareVariationProcess
    {M : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M) :
    ∀ᵐ ω ∂μ,
      HasSquareVariationAlong
        (⟨fun t ↦ M t ω, hM.continuous ω⟩ : C(NNReal, ℝ))
        (fun t ↦ continuousSquareVariationProcess hM t ω) := sorry

end ProbabilityTheory
