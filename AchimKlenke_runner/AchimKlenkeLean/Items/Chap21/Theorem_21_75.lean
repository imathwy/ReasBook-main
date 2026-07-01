import Mathlib
import AchimKlenkeLean.Items.Chap21.Remark_21_67
import AchimKlenkeLean.Items.Chap21.Theorem_21_70

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ

variable {ℱ : TimeFiltration}
variable {M A : NNReal → Ω → ℝ} {τ τ₀ : Ω → ENNReal}

-- Proof sketch: localize `M` before `τ` by the bounded martingale sequence from Remark 21.67,
-- stop again at `τ₀`, and use the integrability of the square-variation witness `A` at `τ₀` to
-- obtain uniform integrability of the doubly stopped martingales. Optional sampling then passes
-- to the limit and identifies the stopped expectation with the initial one.
/-- Theorem 21.75 (1): if `M` is a continuous local martingale up to the stopping time `τ`, if
`τ₀ < τ` is a stopping time, and if `A` is a continuous square-variation process playing the role
of the bracket `⟨M⟩` with `A_{τ₀}` integrable, then `E[M_{τ₀}] = E[M_0]`. -/
theorem expected_stoppedValue_eq_initial_of_localMartingaleUpTo_of_squareVariation_integrable
    (hM : IsContinuousLocalMartingaleUpTo ℱ μ τ M)
    (hτ : IsStoppingTime ℱ τ) (hτ₀ : IsStoppingTime ℱ τ₀) (hτ₀_lt : τ₀ < τ)
    (hA : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAτ₀ : Integrable (stoppedValue A τ₀) μ) :
    μ[stoppedValue M τ₀] = μ[M 0] := sorry

-- Proof sketch: use clause (1) and the square-variation identity for the stopped bounded
-- localizing martingales to obtain a uniform `L²` estimate
-- `E[(M_{t ∧ τ₀})²] ≤ E[M_0²] + E[A_{τ₀}]`. This gives a common `L²` bound in time and, together
-- with the stopped-martingale property, yields that `M^{τ₀}` is an `L²`-bounded martingale.
/-- Theorem 21.75 (2): under the same hypotheses, if `M_0 ∈ L²(μ)`, then the stopped process
`M^{τ₀}` is a martingale and is uniformly bounded in `L²`. -/
theorem stoppedProcess_martingale_and_l2_bounded_of_localMartingaleUpTo_of_memLp_two
    (hM : IsContinuousLocalMartingaleUpTo ℱ μ τ M)
    (hτ : IsStoppingTime ℱ τ) (hτ₀ : IsStoppingTime ℱ τ₀) (hτ₀_lt : τ₀ < τ)
    (hA : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAτ₀ : Integrable (stoppedValue A τ₀) μ)
    (hM0_sq : MemLp (M 0) 2 μ) :
    Martingale (stoppedProcess M τ₀) ℱ μ ∧
      ∃ C : NNReal, ∀ t : NNReal, eLpNorm (stoppedProcess M τ₀ t) 2 μ ≤ C := sorry

end ProbabilityTheory
