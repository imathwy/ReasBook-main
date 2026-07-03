import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_25_26 (from Items/Chap25) -/
open Filter MeasureTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration NNReal mΩ}

local notation "PathSpace" => C(NNReal, ℝ)
local notation "Process" => NNReal → Ω → ℝ

/-- Specializing Exercise 25.2.1(i) to the integrand `t ↦ F' (M_t)` gives convergence in
probability of the left-point partition sums to the Itô integral process `N`. -/
theorem continuousLocalMartingale_comp_deriv_partitionSums_tendstoInMeasure
    {M N : Process} (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) {F : ℝ → ℝ}
    (hFprime_cont : Continuous fun x : ℝ ↦ deriv F x)
    (hN : IsContinuousLocalMartingaleItoIntegral hbr (fun t ω ↦ deriv F (M t ω)) N)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (T : NNReal) :
    TendstoInMeasure μ
      (fun n ω ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ deriv F (M t ω))
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          n)
      atTop
      (N T) := by
  sorry

/-- Remark 25.26: if `M` is a continuous local martingale and
`N_t = ∫₀ᵗ F' (M_s)\,dM_s`, then along a subsequence of any admissible partition sequence the
left-point sums `∑_{t ∈ 𝒫_T^n} F' (M_t) (M_{t'} - M_t)` converge almost surely to `N_T`
simultaneously for every `T ≥ 0`. -/
theorem continuousLocalMartingale_comp_deriv_exists_ae_pathwise_partitionSubsequence
    {M N : Process} (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) {F : ℝ → ℝ}
    (hFprime_cont : Continuous fun x : ℝ ↦ deriv F x)
    (hN : IsContinuousLocalMartingaleItoIntegral hbr (fun t ω ↦ deriv F (M t ω)) N)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        ∀ᵐ ω ∂μ, ∀ T : NNReal,
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun t ↦ deriv F (M t ω))
                (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                P
                T
                (φ n))
            atTop
            (𝓝 (N T ω)) := by
  sorry

end ProbabilityTheory
