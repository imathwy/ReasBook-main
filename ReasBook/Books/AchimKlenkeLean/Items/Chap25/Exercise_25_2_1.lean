import Mathlib
import AchimKlenkeLean.Items.Chap25.ContinuousLocalMartingaleIto
import AchimKlenkeLean.Items.Chap25.Theorem_25_25

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

local notation "PathSpace" => C(NNReal, ℝ)
local notation "Process" => NNReal → Ω → ℝ

variable [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration NNReal mΩ}
variable {M H N : Process}

-- Proof sketch: compare the partition sums with elementary predictable approximants of the
-- continuous integrand `H`, use the Itô isometry for the stopped approximants and the continuity
-- of `H` to control the discretization error, and identify the limit with the chosen Itô integral
-- process `N`.
/-- Exercise 25.2.1 (1): part (i). For every horizon `T`, if `N` is an Itô integral process for
`H` against the continuous local martingale `M`, then the partition sums along any admissible
sequence converge in probability to `N T`. -/
theorem tendstoInMeasure_partitionItoApproximationUpTo
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (hN : IsContinuousLocalMartingaleItoIntegral hbr H N)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) :
    TendstoInMeasure μ
      (fun n ω ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          n)
      atTop
      (N T) := sorry

-- Proof sketch: first obtain convergence in probability at each rational horizon from part (i),
-- then extract a diagonal subsequence. Use continuity of the sample paths of `H`, `M`, and `N`
-- together with the monotonic refinement of the admissible partitions to upgrade the rational-time
-- almost-sure convergence to simultaneous convergence for all `T ≥ 0`.
/-- Exercise 25.2.1 (2): part (ii). There is a subsequence of the admissible partition rows along
which the partition sums converge almost surely to the Itô integral process `N` simultaneously for
every time horizon `T`. -/
theorem exists_partitionSubsequence_with_ae_pathwise_itoApproximation
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (hN : IsContinuousLocalMartingaleItoIntegral hbr H N)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        ∀ᵐ ω ∂μ, ∀ T : NNReal,
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun t ↦ H t ω)
                (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                P
                T
                (φ n))
            atTop
            (𝓝 (N T ω)) := sorry

end ProbabilityTheory
