import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_21_74 (from Items/Chap21) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ

variable {ℱ : TimeFiltration}

-- Proof sketch: use the vanishing-square-variation hypothesis on the sample paths of `A`
-- together with the pathwise identity `⟨M + A⟩ = ⟨M⟩`; then transfer this pathwise statement to
-- the owner-level bracket theorem for the continuous local martingale `hM`.
/-- Corollary 21.74 (1): if `M` is a continuous local martingale and `A` is adapted and
continuous with `⟨A⟩ ≡ 0`, then the continuous square-variation process of `M` is also a
continuous square-variation process of `M + A`; equivalently, `⟨M + A⟩ = ⟨M⟩`. -/
theorem isContinuousSquareVariationProcess_add_of_zeroSquareBracket
    {M A B : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hB : IsContinuousSquareVariationProcess ℱ μ M B)
    (hA_adapted : Adapted ℱ A)
    (hA_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ A t ω)
    (hA_zero_squareVariation :
      ∀ᵐ ω ∂μ, HasSquareVariationAlong ⟨fun t ↦ A t ω, hA_cont ω⟩ 0) :
    IsContinuousSquareVariationProcess ℱ μ (fun t ω ↦ M t ω + A t ω) B := sorry

-- Proof sketch: apply the witness-level square-variation statement above to the canonical bracket
-- `continuousSquareVariationProcess hM` of `M`, then use
-- uniqueness of the canonical bracket for `M + A`.
/-- Corollary 21.74 (1): if `M` is a continuous local martingale and `A` is adapted and
continuous with `⟨A⟩ ≡ 0`, then the canonical bracket of `M + A` agrees with the canonical
bracket of `M`. -/
theorem continuousSquareVariationProcess_add_of_zeroSquareBracket
    {M A : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hMA : IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω + A t ω))
    (hA_adapted : Adapted ℱ A)
    (hA_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ A t ω)
    (hA_zero_squareVariation :
      ∀ᵐ ω ∂μ, HasSquareVariationAlong ⟨fun t ↦ A t ω, hA_cont ω⟩ 0) :
    continuousSquareVariationProcess hMA = continuousSquareVariationProcess hM := sorry

-- Proof sketch: if `M` is a continuous local martingale up to `τ`, the stopped process `M^τ`
-- remains adapted and has continuous paths; the localizing sequence up to `τ` turns into a
-- localizing sequence to `∞` for `stoppedProcess M τ`.
namespace IsContinuousLocalMartingaleUpTo

/-- If `M` is a continuous local martingale up to the stopping time `τ`, then the stopped process
`M^τ` is a continuous local martingale. -/
theorem stoppedProcess
    {M : NNReal → Ω → ℝ} {τ : Ω → ENNReal}
    (hM : IsContinuousLocalMartingaleUpTo ℱ μ τ M) :
    IsContinuousLocalMartingale ℱ μ (stoppedProcess M τ) := sorry

/- If `M` is a continuous local martingale up to the stopping time `τ`, then the stopped process
`M^τ` belongs to `Mlocc ℱ μ`. -/
set_option linter.unusedVariables false in
theorem stoppedProcess_mem_Mlocc
    {M : NNReal → Ω → ℝ} {τ : Ω → ENNReal}
    (hM : IsContinuousLocalMartingaleUpTo ℱ μ τ M) :
    stoppedProcess M τ ∈ Mlocc ℱ μ :=
  IsContinuousLocalMartingaleUpTo.stoppedProcess hM

end IsContinuousLocalMartingaleUpTo

/- Corollary 21.74 (2): the bracket of a continuous local martingale up to `τ` is, by
definition, the canonical bracket of the stopped process `M^τ`; this is the source identity
`⟨M⟩_t = ⟨M^τ⟩_t` used for `t < τ`. -/
#check fun {M : NNReal → Ω → ℝ} {τ : Ω → ENNReal}
    (hM : IsContinuousLocalMartingaleUpTo ℱ μ τ M) ↦
  (continuousSquareVariationProcess hM.stoppedProcess : NNReal → Ω → ℝ)

end ProbabilityTheory
